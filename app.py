"""
Pop-A-Licious Gift Card backend.

Endpoints:
  POST /api/gift-cards/checkout   Create a Stripe Checkout Session for a gift card
  POST /api/webhooks/stripe        Stripe webhook: issues the gift card code + emails recipient
  GET  /api/gift-cards/balance    Look up a gift card balance by code
  POST /api/gift-cards/redeem      Redeem an amount from a gift card code
  GET  /healthz                    Health check

Env vars (see .env.example):
  STRIPE_SECRET_KEY, STRIPE_WEBHOOK_SECRET, RESEND_API_KEY,
  EMAIL_FROM, SITE_URL, DATABASE_PATH, GIFT_CARD_PRODUCT_ID
"""

import json
import os
import re
import secrets
import sqlite3
import string
import hmac
import hashlib
import base64
import html
from datetime import datetime, timedelta, timezone
from urllib.parse import urlencode

import requests
import stripe
from flask import Flask, jsonify, redirect, request
from flask_cors import CORS
from itsdangerous import BadSignature, SignatureExpired, URLSafeTimedSerializer
from werkzeug.security import check_password_hash, generate_password_hash

# ---------------------------------------------------------------- config

STRIPE_SECRET_KEY = os.environ["STRIPE_SECRET_KEY"]
STRIPE_WEBHOOK_SECRET = os.environ["STRIPE_WEBHOOK_SECRET"]
STRIPE_PUBLISHABLE_KEY = os.environ.get("STRIPE_PUBLISHABLE_KEY", "")
RESEND_API_KEY = os.environ["RESEND_API_KEY"]
CORS_ORIGINS = os.environ.get("CORS_ORIGINS", "https://muse.ai")
EMAIL_FROM = os.environ.get("EMAIL_FROM", "Pop-A-Licious <noreply@pop-a-licious.com>")
SITE_URL = os.environ.get("SITE_URL", "https://pop-a-licious.com").rstrip("/")
DATABASE_PATH = os.environ.get("DATABASE_PATH", "giftcards.db")
GIFT_CARD_PRODUCT_ID = os.environ.get("GIFT_CARD_PRODUCT_ID", "prod_VPQOMcf52Y1mlg")

# Shippo (cheapest-rate shipping lookup)
SHIPPO_API_KEY = os.environ.get("SHIPPO_API_KEY", "")
# Printful (merch POD fulfillment)
PRINTFUL_API_KEY = os.environ.get("PRINTFUL_API_KEY", "")
SHIP_FROM = {
    "name": "Pop-A-Licious",
    "street1": os.environ.get("SHIP_FROM_STREET1", "2013 Angel Falls Dr."),
    "city": os.environ.get("SHIP_FROM_CITY", "Henderson"),
    "state": os.environ.get("SHIP_FROM_STATE", "NV"),
    "zip": os.environ.get("SHIP_FROM_ZIP", "89074"),
    "country": "US",
}

# Customer accounts (login page)
# AUTH_SECRET signs the login tokens — set it to any long random string.
# GOOGLE_CLIENT_ID/SECRET enable the "Continue with Google" button
# (from Google Cloud Console; redirect URI is BACKEND_URL + /api/auth/google/callback).
AUTH_SECRET = os.environ.get("AUTH_SECRET", "")
GOOGLE_CLIENT_ID = os.environ.get("GOOGLE_CLIENT_ID", "")
GOOGLE_CLIENT_SECRET = os.environ.get("GOOGLE_CLIENT_SECRET", "")
BACKEND_URL = os.environ.get(
    "BACKEND_URL", "https://popalicious-gift-cards-production.up.railway.app"
).rstrip("/")

# Promo codes shown on the site's Offers & Discounts page.
# percent -> Stripe percent-off coupon (one use). free_shipping -> zeroes the
# shipping line when the merchandise subtotal meets the minimum.
PROMOS = {
    "RELAUNCH15": {
        "type": "percent", "percent_off": 15,
        "label": "Grand Re-Launch",
        "description": "15% off your order",
    },
    "WELCOME10": {
        "type": "percent", "percent_off": 10,
        "label": "Newsletter Signup",
        "description": "10% off your order",
    },
    "FREESHIP50": {
        "type": "free_shipping", "min_subtotal_cents": 5000,
        "label": "Free Shipping $50+",
        "description": "Free shipping on orders of $50 or more",
    },
}

MIN_AMOUNT_CENTS = 500      # $5
MAX_AMOUNT_CENTS = 50000    # $500
# When true, the gift card checkout also accepts a $0.50 test amount
# (for the hidden pre-launch test gift card page). Turn off when live.
ALLOW_TEST_AMOUNTS = os.environ.get("ALLOW_TEST_AMOUNTS", "").lower() == "true"

# Default subscription renewal reminder email template (seeded into
# subscription_email_templates on init; admins can edit it live).
_SUBSCRIPTION_REMINDER_SUBJECT = "Your Pop-A-Licious subscription renews in 3 days"
_SUBSCRIPTION_REMINDER_BODY = """\
<html><body style="font-family: Arial, sans-serif; line-height: 1.6; color: #333;">
<p style="text-align:center;"><img src="https://pop-a-licious.com/logo.png" alt="Pop-A-Licious" style="max-width:220px;"></p>
<p>Hi {{name}},</p>
<p>Just a heads-up: your Pop-A-Licious subscription (<strong>{{frequency_label}}</strong>) renews on <strong>{{billing_date}}</strong>.</p>
<p><strong>Your upcoming box:</strong> {{flavors}}<br>
<strong>Bags:</strong> {{bags}}<br>
<strong>Estimated total:</strong> {{total}} (includes estimated shipping)</p>
<p>Want to change your flavors before we pop them fresh? Review and confirm below:</p>
<p style="text-align:center;"><a href="{{confirm_url}}" style="display:inline-block;background:#e63946;color:#ffffff;text-decoration:none;padding:14px 28px;border-radius:8px;font-weight:bold;">Review &amp; Confirm Your Flavors</a></p>
<p>If everything looks good, you don't need to do a thing &mdash; we'll charge your card on file and get popping!</p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>
</body></html>"""

stripe.api_key = STRIPE_SECRET_KEY

app = Flask(__name__)
_cors_origins = "*" if CORS_ORIGINS.strip() == "*" else [o.strip() for o in CORS_ORIGINS.split(",") if o.strip()]
CORS(app, origins=_cors_origins, supports_credentials=True,
     allow_headers=["Content-Type", "Authorization"])

# ---------------------------------------------------------------- db

def db():
    conn = sqlite3.connect(DATABASE_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    conn = db()
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS gift_cards (
            code TEXT PRIMARY KEY,
            amount_cents INTEGER NOT NULL,
            balance_cents INTEGER NOT NULL,
            purchaser_name TEXT NOT NULL,
            purchaser_email TEXT NOT NULL,
            recipient_name TEXT NOT NULL,
            recipient_email TEXT NOT NULL,
            message TEXT,
            stripe_session_id TEXT,
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS redemptions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            code TEXT NOT NULL,
            amount_cents INTEGER NOT NULL,
            order_ref TEXT,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            stripe_session_id TEXT UNIQUE NOT NULL,
            email TEXT,
            customer_name TEXT NOT NULL DEFAULT '',
            shipping_address TEXT NOT NULL DEFAULT '',
            items_summary TEXT,
            amount_total_cents INTEGER,
            gift_card_code TEXT,
            gift_card_discount_cents INTEGER,
            promo_code TEXT NOT NULL DEFAULT '',
            reward_code TEXT NOT NULL DEFAULT '',
            total_qty INTEGER NOT NULL DEFAULT 0,
            shippo_label_url TEXT NOT NULL DEFAULT '',
            shippo_tracking_number TEXT NOT NULL DEFAULT '',
            shippo_label_created_at TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS promo_redemptions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            code TEXT NOT NULL,
            email TEXT NOT NULL,
            stripe_session_id TEXT,
            created_at TEXT NOT NULL,
            UNIQUE(code, email)
        );
        CREATE TABLE IF NOT EXISTS paypal_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            paypal_order_id TEXT UNIQUE NOT NULL,
            email TEXT,
            items_summary TEXT,
            gift_card_code TEXT,
            gift_card_discount_cents INTEGER,
            promo_code TEXT,
            reward_code TEXT NOT NULL DEFAULT '',
            amount_total_cents INTEGER,
            total_qty INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT UNIQUE NOT NULL,
            name TEXT NOT NULL DEFAULT '',
            password_hash TEXT NOT NULL DEFAULT '',
            verified INTEGER NOT NULL DEFAULT 0,
            google_id TEXT NOT NULL DEFAULT '',
            birthday TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS verification_tokens (
            token TEXT PRIMARY KEY,
            user_id INTEGER NOT NULL,
            expires_at TEXT NOT NULL,
            used INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS password_reset_tokens (
            token TEXT PRIMARY KEY,
            user_id INTEGER NOT NULL,
            expires_at TEXT NOT NULL,
            used INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS site_visits (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            session_id TEXT NOT NULL DEFAULT '',
            path TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS cart_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            session_id TEXT NOT NULL DEFAULT '',
            email TEXT NOT NULL DEFAULT '',
            items_summary TEXT NOT NULL DEFAULT '',
            item_count INTEGER NOT NULL DEFAULT 0,
            ordered INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS abandoned_carts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT NOT NULL,
            session_id TEXT NOT NULL DEFAULT '',
            items_json TEXT NOT NULL DEFAULT '[]',
            items_summary TEXT NOT NULL DEFAULT '',
            item_count INTEGER NOT NULL DEFAULT 0,
            subtotal_cents INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'pending',
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            sent_at TEXT
        );
        CREATE TABLE IF NOT EXISTS subscription_requests (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT NOT NULL DEFAULT '',
            name TEXT NOT NULL DEFAULT '',
            config TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS reviews (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            flavor_slug TEXT NOT NULL,
            user_id INTEGER NOT NULL,
            user_name TEXT NOT NULL,
            rating INTEGER NOT NULL,
            text TEXT NOT NULL,
            approved INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL,
            UNIQUE(flavor_slug, user_id)
        );
        CREATE TABLE IF NOT EXISTS kernel_transactions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            kernels INTEGER NOT NULL,
            reason TEXT NOT NULL,
            order_ref TEXT NOT NULL DEFAULT '',
            staff_id INTEGER,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS staff (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT UNIQUE NOT NULL,
            name TEXT NOT NULL DEFAULT '',
            password_hash TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            headshot TEXT NOT NULL DEFAULT '',
            kernels INTEGER NOT NULL DEFAULT 0,
            birthday TEXT NOT NULL DEFAULT '',
            hire_date TEXT NOT NULL DEFAULT '',
            referral_code TEXT NOT NULL DEFAULT '',
            verified INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS staff_kernel_transactions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            staff_id INTEGER NOT NULL,
            kernels INTEGER NOT NULL,
            reason TEXT NOT NULL,
            ref TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS staff_verification_tokens (
            token TEXT PRIMARY KEY,
            staff_id INTEGER NOT NULL,
            expires_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS staff_password_reset_tokens (
            token TEXT PRIMARY KEY,
            staff_id INTEGER NOT NULL,
            expires_at TEXT NOT NULL,
            used INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS loyalty_rewards (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            reward_type TEXT NOT NULL,
            code TEXT UNIQUE NOT NULL,
            kernels_spent INTEGER NOT NULL DEFAULT 0,
            used INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL,
            used_at TEXT NOT NULL DEFAULT '',
            staff_id INTEGER NOT NULL DEFAULT 0
        );
        """
    )
    # Migration for databases created before the approved column existed.
    cols = [r["name"] for r in conn.execute("PRAGMA table_info(reviews)").fetchall()]
    if "approved" not in cols:
        conn.execute("ALTER TABLE reviews ADD COLUMN approved INTEGER NOT NULL DEFAULT 0")
    # Migration: birthday field for the loyalty birthday reward.
    ucols = [r["name"] for r in conn.execute("PRAGMA table_info(users)").fetchall()]
    if "birthday" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN birthday TEXT NOT NULL DEFAULT ''")
    # Migration: active flag for admin customer deactivation.
    if "active" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN active INTEGER NOT NULL DEFAULT 1")
    # Migration: anniversary kernels + login kernel notifications.
    if "anniversary_credited_year" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN anniversary_credited_year INTEGER NOT NULL DEFAULT 0")
    if "last_notified_balance" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN last_notified_balance INTEGER NOT NULL DEFAULT 0")
    # Migration: richer order details for the admin order view.
    ocols = [r["name"] for r in conn.execute("PRAGMA table_info(orders)").fetchall()]
    for col in ("customer_name", "shipping_address", "promo_code", "reward_code"):
        if col not in ocols:
            conn.execute(f"ALTER TABLE orders ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
    # Migration: Shippo label fields + bag count (for label weight) on orders.
    for col in ("shippo_label_url", "shippo_tracking_number", "shippo_label_created_at"):
        if col not in ocols:
            conn.execute(f"ALTER TABLE orders ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
    if "total_qty" not in ocols:
        conn.execute("ALTER TABLE orders ADD COLUMN total_qty INTEGER NOT NULL DEFAULT 0")
    # Migration: Printful merch fulfillment fields on orders.
    for col in ("printful_order_id", "printful_status", "printful_tracking", "printful_carrier"):
        if col not in ocols:
            conn.execute(f"ALTER TABLE orders ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
    # Migration: Shippo label fields on fundraiser orders.
    # (Table may not exist yet on very old DBs — init_db creates it below.)
    fexists = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='fundraiser_orders'"
    ).fetchone()
    if fexists:
        focols = [r["name"] for r in conn.execute("PRAGMA table_info(fundraiser_orders)").fetchall()]
        for col in ("shippo_label_url", "shippo_tracking_number", "shippo_label_created_at"):
            if col not in focols:
                conn.execute(f"ALTER TABLE fundraiser_orders ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
    # Migration: bag count on paypal_orders (for label weight).
    pcols = [r["name"] for r in conn.execute("PRAGMA table_info(paypal_orders)").fetchall()]
    if "total_qty" not in pcols:
        conn.execute("ALTER TABLE paypal_orders ADD COLUMN total_qty INTEGER NOT NULL DEFAULT 0")
    # Migration: staff_id on loyalty_rewards for employee redemptions.
    lrcols = [r["name"] for r in conn.execute("PRAGMA table_info(loyalty_rewards)").fetchall()]
    if "staff_id" not in lrcols:
        conn.execute("ALTER TABLE loyalty_rewards ADD COLUMN staff_id INTEGER NOT NULL DEFAULT 0")
    # Migration: staff headshots, kernel balances, and staff kernel ledger.
    scols = [r["name"] for r in conn.execute("PRAGMA table_info(staff)").fetchall()]
    if "headshot" not in scols:
        conn.execute("ALTER TABLE staff ADD COLUMN headshot TEXT NOT NULL DEFAULT ''")
    if "kernels" not in scols:
        conn.execute("ALTER TABLE staff ADD COLUMN kernels INTEGER NOT NULL DEFAULT 0")
    if "birthday" not in scols:
        conn.execute("ALTER TABLE staff ADD COLUMN birthday TEXT NOT NULL DEFAULT ''")
    if "hire_date" not in scols:
        conn.execute("ALTER TABLE staff ADD COLUMN hire_date TEXT NOT NULL DEFAULT ''")
    if "referral_code" not in scols:
        conn.execute("ALTER TABLE staff ADD COLUMN referral_code TEXT NOT NULL DEFAULT ''")
    if "verified" not in scols:
        conn.execute("ALTER TABLE staff ADD COLUMN verified INTEGER NOT NULL DEFAULT 1")
    conn.execute(
        """CREATE TABLE IF NOT EXISTS staff_verification_tokens (
            token TEXT PRIMARY KEY,
            staff_id INTEGER NOT NULL,
            expires_at TEXT NOT NULL
        )"""
    )
    # Backfill referral codes for existing staff.
    for r in conn.execute("SELECT id FROM staff WHERE referral_code = ''").fetchall():
        code = "STF-" + secrets.token_hex(3).upper()
        conn.execute("UPDATE staff SET referral_code = ? WHERE id = ?", (code, r["id"]))
    conn.execute(
        """CREATE TABLE IF NOT EXISTS staff_kernel_transactions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            staff_id INTEGER NOT NULL,
            kernels INTEGER NOT NULL,
            reason TEXT NOT NULL,
            ref TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        )"""
    )
    # Migration: reward_code on paypal_orders for loyalty reward redemption.
    pcols = [r["name"] for r in conn.execute("PRAGMA table_info(paypal_orders)").fetchall()]
    if "reward_code" not in pcols:
        conn.execute("ALTER TABLE paypal_orders ADD COLUMN reward_code TEXT NOT NULL DEFAULT ''")
    # ---- Fundraising + Subscriptions tables (PART 1 & PART 2) ----
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS fundraisers (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            code TEXT UNIQUE NOT NULL,
            org_name TEXT NOT NULL DEFAULT '',
            contact_name TEXT NOT NULL DEFAULT '',
            contact_email TEXT NOT NULL DEFAULT '',
            goal_cents INTEGER NOT NULL DEFAULT 0,
            start_date TEXT NOT NULL DEFAULT '',
            end_date TEXT NOT NULL DEFAULT '',
            event_days INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'active',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS fundraiser_teams (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fundraiser_id INTEGER NOT NULL,
            name TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS fundraiser_sellers (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fundraiser_id INTEGER NOT NULL,
            team_id INTEGER NOT NULL DEFAULT 0,
            name TEXT NOT NULL DEFAULT '',
            email TEXT NOT NULL DEFAULT '',
            referral_code TEXT UNIQUE NOT NULL,
            video_url TEXT NOT NULL DEFAULT '',
            personal_goal_cents INTEGER NOT NULL DEFAULT 0,
            shared INTEGER NOT NULL DEFAULT 0,
            nudged INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS fundraiser_stretch_goals (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fundraiser_id INTEGER NOT NULL,
            threshold_cents INTEGER NOT NULL DEFAULT 0,
            label TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS fundraiser_sponsors (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fundraiser_id INTEGER NOT NULL,
            business_name TEXT NOT NULL DEFAULT '',
            match_cap_cents INTEGER NOT NULL DEFAULT 0,
            matched_cents INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS fundraiser_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fundraiser_id INTEGER NOT NULL,
            seller_id INTEGER NOT NULL DEFAULT 0,
            order_number TEXT UNIQUE NOT NULL,
            customer_name TEXT NOT NULL DEFAULT '',
            customer_email TEXT NOT NULL DEFAULT '',
            ship_name TEXT NOT NULL DEFAULT '',
            ship_street TEXT NOT NULL DEFAULT '',
            ship_city TEXT NOT NULL DEFAULT '',
            ship_state TEXT NOT NULL DEFAULT '',
            ship_zip TEXT NOT NULL DEFAULT '',
            items TEXT NOT NULL DEFAULT '[]',
            subtotal_cents INTEGER NOT NULL DEFAULT 0,
            donation_cents INTEGER NOT NULL DEFAULT 0,
            roundup_cents INTEGER NOT NULL DEFAULT 0,
            shipping_cents INTEGER NOT NULL DEFAULT 0,
            total_cents INTEGER NOT NULL DEFAULT 0,
            stripe_payment_intent_id TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'paid',
            shippo_label_url TEXT NOT NULL DEFAULT '',
            shippo_tracking_number TEXT NOT NULL DEFAULT '',
            shippo_label_created_at TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS fundraiser_ticker (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fundraiser_id INTEGER NOT NULL,
            message TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS subscriptions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            stripe_customer_id TEXT NOT NULL DEFAULT '',
            stripe_payment_method_id TEXT NOT NULL DEFAULT '',
            items TEXT NOT NULL DEFAULT '[]',
            frequency TEXT NOT NULL DEFAULT 'monthly',
            discount_percent INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'active',
            next_billing_date TEXT NOT NULL DEFAULT '',
            ship_name TEXT NOT NULL DEFAULT '',
            ship_street TEXT NOT NULL DEFAULT '',
            ship_city TEXT NOT NULL DEFAULT '',
            ship_state TEXT NOT NULL DEFAULT '',
            ship_zip TEXT NOT NULL DEFAULT '',
            ship_email TEXT NOT NULL DEFAULT '',
            last_billed_at TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS subscription_renewals (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            subscription_id INTEGER NOT NULL,
            billing_date TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'pending',
            confirm_token TEXT UNIQUE,
            reminder_sent_at TEXT NOT NULL DEFAULT '',
            charged_at TEXT NOT NULL DEFAULT '',
            order_id INTEGER NOT NULL DEFAULT 0,
            amount_cents INTEGER NOT NULL DEFAULT 0
        );
        """
    )
    # Migration: failed_attempts counter for renewal retry logic.
    try:
        conn.execute("ALTER TABLE subscription_renewals ADD COLUMN failed_attempts INTEGER NOT NULL DEFAULT 0")
    except sqlite3.OperationalError:
        pass
    # Migration: prevent duplicate renewals for the same billing date.
    try:
        conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_renewals_sub_date ON subscription_renewals (subscription_id, billing_date)")
    except sqlite3.OperationalError:
        pass
    # Migration: demo-mode flag on order-like tables (never billed, never shipped).
    for _t in ("orders", "fundraiser_orders", "gift_cards", "subscriptions"):
        try:
            conn.execute(f"ALTER TABLE {_t} ADD COLUMN is_demo INTEGER NOT NULL DEFAULT 0")
        except sqlite3.OperationalError:
            pass
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS subscription_email_templates (
            name TEXT PRIMARY KEY,
            subject TEXT NOT NULL DEFAULT '',
            body_html TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS marketing_unsubscribes (
            email TEXT PRIMARY KEY,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS marketing_campaigns (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL DEFAULT '',
            subject TEXT NOT NULL,
            audience TEXT NOT NULL DEFAULT 'all',
            recipient_count INTEGER NOT NULL DEFAULT 0,
            sent_at TEXT NOT NULL
        );
        """
    )
    # Migration: Stripe customer id on users for subscription billing.
    if "stripe_customer_id" not in ucols:
        conn.execute("ALTER TABLE users ADD COLUMN stripe_customer_id TEXT NOT NULL DEFAULT ''")
    # Seed the subscription reminder email template (only if missing —
    # never overwrite an admin's customized template).
    conn.execute(
        """INSERT OR IGNORE INTO subscription_email_templates
           (name, subject, body_html, updated_at) VALUES (?, ?, ?, ?)""",
        ("reminder", _SUBSCRIPTION_REMINDER_SUBJECT, _SUBSCRIPTION_REMINDER_BODY,
         datetime.now(timezone.utc).isoformat()),
    )
    # ---------------- ERP Phase 1 tables ----------------
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS erp_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sku TEXT UNIQUE NOT NULL,
            name TEXT NOT NULL,
            type TEXT NOT NULL,
            unit TEXT NOT NULL DEFAULT 'each',
            track_lots INTEGER NOT NULL DEFAULT 0,
            avg_cost_cents INTEGER NOT NULL DEFAULT 0,
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_locations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            code TEXT UNIQUE NOT NULL,
            name TEXT NOT NULL,
            type TEXT NOT NULL,
            active INTEGER NOT NULL DEFAULT 1
        );
        CREATE TABLE IF NOT EXISTS erp_stock_ledger (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            item_id INTEGER NOT NULL,
            location_id INTEGER NOT NULL,
            qty_change REAL NOT NULL,
            movement_type TEXT NOT NULL,
            ref_type TEXT NOT NULL DEFAULT '',
            ref_id TEXT NOT NULL DEFAULT '',
            lot_code TEXT NOT NULL DEFAULT '',
            unit_cost_cents INTEGER NOT NULL DEFAULT 0,
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL,
            note TEXT NOT NULL DEFAULT ''
        );
        CREATE INDEX IF NOT EXISTS idx_erp_ledger_item_loc ON erp_stock_ledger (item_id, location_id);
        CREATE TABLE IF NOT EXISTS erp_lots (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            lot_code TEXT NOT NULL,
            item_id INTEGER NOT NULL,
            supplier_lot TEXT NOT NULL DEFAULT '',
            received_date TEXT NOT NULL DEFAULT '',
            expiry_date TEXT NOT NULL DEFAULT '',
            location_id INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS erp_vendors (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            contact_name TEXT NOT NULL DEFAULT '',
            email TEXT NOT NULL DEFAULT '',
            phone TEXT NOT NULL DEFAULT '',
            payment_terms TEXT NOT NULL DEFAULT '',
            lead_time_days INTEGER NOT NULL DEFAULT 0,
            notes TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_purchase_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            po_number TEXT UNIQUE NOT NULL,
            vendor_id INTEGER NOT NULL,
            status TEXT NOT NULL DEFAULT 'draft',
            order_date TEXT NOT NULL,
            expected_date TEXT NOT NULL DEFAULT '',
            freight_cents INTEGER NOT NULL DEFAULT 0,
            tax_cents INTEGER NOT NULL DEFAULT 0,
            notes TEXT NOT NULL DEFAULT '',
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_po_lines (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            po_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            qty_ordered REAL NOT NULL,
            qty_received REAL NOT NULL DEFAULT 0,
            unit_cost_cents INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_reorder_rules (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            item_id INTEGER NOT NULL,
            location_id INTEGER NOT NULL,
            reorder_point REAL NOT NULL,
            reorder_qty REAL NOT NULL DEFAULT 0,
            preferred_vendor_id INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_recipes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            batch_size_bags REAL NOT NULL DEFAULT 0,
            version INTEGER NOT NULL DEFAULT 1,
            active INTEGER NOT NULL DEFAULT 1,
            notes TEXT NOT NULL DEFAULT '',
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_recipe_lines (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            recipe_id INTEGER NOT NULL,
            recipe_version INTEGER NOT NULL DEFAULT 1,
            item_id INTEGER NOT NULL,
            qty_per_batch REAL NOT NULL,
            unit TEXT NOT NULL DEFAULT 'each',
            notes TEXT NOT NULL DEFAULT ''
        );
        CREATE INDEX IF NOT EXISTS idx_erp_recipe_lines ON erp_recipe_lines (recipe_id, recipe_version);
        CREATE TABLE IF NOT EXISTS erp_production_batches (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            batch_number TEXT UNIQUE NOT NULL,
            recipe_id INTEGER NOT NULL,
            recipe_version INTEGER NOT NULL DEFAULT 1,
            planned_qty_bags REAL NOT NULL,
            actual_qty_bags REAL NOT NULL DEFAULT 0,
            waste_qty_bags REAL NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'planned',
            lot_code TEXT NOT NULL DEFAULT '',
            expiry_date TEXT NOT NULL DEFAULT '',
            location_id INTEGER NOT NULL,
            order_ref TEXT NOT NULL DEFAULT '',
            total_cost_cents INTEGER NOT NULL DEFAULT 0,
            produced_by TEXT NOT NULL DEFAULT '',
            started_at TEXT NOT NULL DEFAULT '',
            completed_at TEXT NOT NULL DEFAULT '',
            notes TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_batch_ingredients (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            batch_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            lot_code TEXT NOT NULL DEFAULT '',
            qty_used REAL NOT NULL,
            unit TEXT NOT NULL DEFAULT 'each',
            unit_cost_cents INTEGER NOT NULL DEFAULT 0
        );
        CREATE INDEX IF NOT EXISTS idx_erp_batch_ingredients ON erp_batch_ingredients (batch_id);
        CREATE TABLE IF NOT EXISTS erp_wholesale_accounts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            contact_name TEXT NOT NULL DEFAULT '',
            email TEXT NOT NULL DEFAULT '',
            phone TEXT NOT NULL DEFAULT '',
            address TEXT NOT NULL DEFAULT '',
            price_per_bag_cents INTEGER NOT NULL DEFAULT 400,
            payment_terms TEXT NOT NULL DEFAULT '',
            notes TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_wholesale_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_number TEXT UNIQUE NOT NULL,
            account_id INTEGER NOT NULL,
            status TEXT NOT NULL DEFAULT 'new',
            order_date TEXT NOT NULL DEFAULT '',
            due_date TEXT NOT NULL DEFAULT '',
            notes TEXT NOT NULL DEFAULT '',
            via_edi INTEGER NOT NULL DEFAULT 0,
            edi_document_id INTEGER NOT NULL DEFAULT 0,
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_wholesale_order_lines (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_id INTEGER NOT NULL,
            flavor_name TEXT NOT NULL,
            qty_bags REAL NOT NULL,
            unit_price_cents INTEGER NOT NULL,
            line_total_cents INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_erp_wholesale_lines ON erp_wholesale_order_lines (order_id);
        CREATE TABLE IF NOT EXISTS erp_order_fulfillment (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_source TEXT NOT NULL,
            order_id INTEGER NOT NULL,
            status TEXT NOT NULL DEFAULT 'new',
            updated_by TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL,
            note TEXT NOT NULL DEFAULT ''
        );
        CREATE UNIQUE INDEX IF NOT EXISTS uidx_erp_fulfillment ON erp_order_fulfillment (order_source, order_id);
        CREATE TABLE IF NOT EXISTS erp_fulfillment_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_source TEXT NOT NULL,
            order_id INTEGER NOT NULL,
            status TEXT NOT NULL,
            updated_by TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL,
            note TEXT NOT NULL DEFAULT ''
        );
        CREATE INDEX IF NOT EXISTS idx_erp_fulfillment_hist ON erp_fulfillment_history (order_source, order_id);
        CREATE TABLE IF NOT EXISTS erp_batch_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            batch_id INTEGER NOT NULL,
            order_source TEXT NOT NULL,
            order_id INTEGER NOT NULL,
            qty_bags REAL NOT NULL,
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_erp_batch_orders_batch ON erp_batch_orders (batch_id);
        CREATE INDEX IF NOT EXISTS idx_erp_batch_orders_order ON erp_batch_orders (order_source, order_id);
        CREATE TABLE IF NOT EXISTS erp_edi_partners (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            provider TEXT NOT NULL DEFAULT '',
            transport TEXT NOT NULL DEFAULT 'manual-file',
            config_json TEXT NOT NULL DEFAULT '{}',
            active INTEGER NOT NULL DEFAULT 1,
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS erp_edi_documents (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            partner_id INTEGER NOT NULL DEFAULT 0,
            direction TEXT NOT NULL,
            doc_type TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'received',
            raw_text TEXT NOT NULL DEFAULT '',
            parsed_json TEXT NOT NULL DEFAULT '{}',
            order_source TEXT NOT NULL DEFAULT '',
            order_id INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_erp_edi_docs ON erp_edi_documents (partner_id, direction, doc_type, status);
        CREATE TABLE IF NOT EXISTS erp_qb_oauth (
            id INTEGER PRIMARY KEY CHECK (id = 1),
            access_token TEXT NOT NULL DEFAULT '',
            refresh_token TEXT NOT NULL DEFAULT '',
            expires_at INTEGER NOT NULL DEFAULT 0,
            realm_id TEXT NOT NULL DEFAULT '',
            company_name TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS erp_qb_links (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            entity_type TEXT NOT NULL,
            entity_id INTEGER NOT NULL,
            qb_object TEXT NOT NULL,
            qb_id TEXT NOT NULL,
            pushed_at TEXT NOT NULL,
            pushed_by TEXT NOT NULL DEFAULT ''
        );
        CREATE UNIQUE INDEX IF NOT EXISTS uidx_erp_qb_links ON erp_qb_links (entity_type, entity_id, qb_object);
        CREATE TABLE IF NOT EXISTS erp_qb_config (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS erp_sales_summaries (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            period_start TEXT NOT NULL,
            period_end TEXT NOT NULL,
            channel TEXT NOT NULL DEFAULT 'online',
            total_cents INTEGER NOT NULL DEFAULT 0,
            order_count INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'draft',
            created_by TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );
        CREATE UNIQUE INDEX IF NOT EXISTS uidx_erp_sales_summaries ON erp_sales_summaries (period_start, period_end, channel);
        -- ERP Phase 5: wholesale customer portal tables --
        CREATE TABLE IF NOT EXISTS erp_wholesale_users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id INTEGER NOT NULL,
            email TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL DEFAULT '',
            invite_token TEXT NOT NULL DEFAULT '',
            invite_expires_at TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_erp_wholesale_users_acct ON erp_wholesale_users (account_id);
        CREATE TABLE IF NOT EXISTS erp_wholesale_addresses (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id INTEGER NOT NULL,
            label TEXT NOT NULL DEFAULT '',
            street TEXT NOT NULL DEFAULT '',
            city TEXT NOT NULL DEFAULT '',
            state TEXT NOT NULL DEFAULT '',
            zip TEXT NOT NULL DEFAULT '',
            phone TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_erp_wholesale_addrs ON erp_wholesale_addresses (account_id);
        CREATE TABLE IF NOT EXISTS erp_flavor_categories (
            flavor_name TEXT PRIMARY KEY,
            category TEXT NOT NULL DEFAULT 'sweet'
        );
        CREATE TABLE IF NOT EXISTS erp_order_production_lines (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            order_id INTEGER NOT NULL,
            flavor_name TEXT NOT NULL,
            qty_bags REAL NOT NULL,
            done INTEGER NOT NULL DEFAULT 0,
            done_by TEXT NOT NULL DEFAULT '',
            done_at TEXT NOT NULL DEFAULT ''
        );
        CREATE INDEX IF NOT EXISTS idx_erp_prod_lines ON erp_order_production_lines (order_id);
        INSERT OR IGNORE INTO erp_locations (code, name, type, active) VALUES
         ('HEND', 'Henderson Warehouse', 'warehouse', 1),
         ('EVT', 'Events / Mobile', 'mobile', 1),
         ('PFUL', 'Printful (virtual)', 'virtual', 1);
        """
    )
    # ERP Phase 5 migrations: new columns on wholesale accounts/orders for the
    # customer portal (guarded for databases created before these columns existed).
    wacols = [r["name"] for r in conn.execute("PRAGMA table_info(erp_wholesale_accounts)").fetchall()]
    for col, ddl in (("contact_person", "TEXT NOT NULL DEFAULT ''"),
                     ("savory_price_cents", "INTEGER NOT NULL DEFAULT 400"),
                     ("sweet_price_cents", "INTEGER NOT NULL DEFAULT 400"),
                     ("default_po", "TEXT NOT NULL DEFAULT ''"),
                     ("pricing_mode", "TEXT NOT NULL DEFAULT 'bag'"),
                     ("account_status", "TEXT NOT NULL DEFAULT 'active'")):
        if col not in wacols:
            conn.execute("ALTER TABLE erp_wholesale_accounts ADD COLUMN %s %s" % (col, ddl))
    wocols = [r["name"] for r in conn.execute("PRAGMA table_info(erp_wholesale_orders)").fetchall()]
    for col, ddl in (("po_number", "TEXT NOT NULL DEFAULT ''"),
                     ("address_id", "INTEGER NOT NULL DEFAULT 0"),
                     ("pricing_mode", "TEXT NOT NULL DEFAULT 'bag'"),
                     ("placed_by_user_id", "INTEGER NOT NULL DEFAULT 0")):
        if col not in wocols:
            conn.execute("ALTER TABLE erp_wholesale_orders ADD COLUMN %s %s" % (col, ddl))
    wacols2 = [r["name"] for r in conn.execute("PRAGMA table_info(erp_wholesale_addresses)").fetchall()]
    for col, ddl in (("location_name", "TEXT NOT NULL DEFAULT ''"),
                     ("contact_name", "TEXT NOT NULL DEFAULT ''"),
                     ("contact_email", "TEXT NOT NULL DEFAULT ''"),
                     ("contact_phone", "TEXT NOT NULL DEFAULT ''")):
        if col not in wacols2:
            conn.execute("ALTER TABLE erp_wholesale_addresses ADD COLUMN %s %s" % (col, ddl))
    # Backfill one delivery location per account that still only has the legacy
    # free-text address and no structured locations yet.
    for _a in conn.execute("SELECT id, address FROM erp_wholesale_accounts").fetchall():
        if (_a["address"] or "").strip():
            _n = conn.execute("SELECT COUNT(*) AS c FROM erp_wholesale_addresses"
                              " WHERE account_id = ?", (_a["id"],)).fetchone()["c"]
            if not _n:
                conn.execute("INSERT INTO erp_wholesale_addresses (account_id,"
                             " location_name, street, active, created_at)"
                             " VALUES (?, 'Main location', ?, 1, ?)",
                             (_a["id"], _a["address"].strip(),
                              datetime.now(timezone.utc).isoformat()))
    # Seed flavor categories (spec §4; the user may correct via the API).
    for _flv, _cat in (
            ("Bacon", "savory"), ("Buffalo Ranch", "savory"),
            ("Cheddar", "savory"), ("Cheddar Jalapeño", "savory"),
            ("Cheeseburger", "savory"), ("Dill Pickle", "savory"),
            ("Garlic Butter", "savory"), ("Garlic Parmesan", "savory"),
            ("Nashville Hot", "savory"), ("Pizza", "savory"),
            ("Salt and Vinegar", "savory"), ("White Cheddar", "savory"),
            ("Alien Mix", "sweet"), ("Banana Pudding", "sweet"),
            ("Birthday Cake", "sweet"), ("Caramel", "sweet"),
            ("Churro", "sweet"), ("Cinnamon Roll", "sweet"),
            ("Cookie and Cream", "sweet"), ("Kettle Corn", "sweet"),
            ("Lemonade", "sweet"), ("Muddy Buddy", "sweet"),
            ("Snickerdoodle", "sweet"),
            ("Strawberry Cheesecake", "sweet"), ("Sugar Cookie", "sweet")):
        conn.execute("INSERT OR IGNORE INTO erp_flavor_categories (flavor_name, category)"
                     " VALUES (?, ?)", (_flv, _cat))
    conn.commit()
    conn.close()

# The database must live on persistent storage (e.g. a Railway Volume).
# If it can't be opened, keep the app up but report it on /healthz instead
# of crashing the whole service.
DB_OK = True
DB_ERROR = None
try:
    parent = os.path.dirname(os.path.abspath(DATABASE_PATH))
    os.makedirs(parent, exist_ok=True)
    init_db()
except Exception as e:
    DB_OK = False
    DB_ERROR = f"{type(e).__name__}: {e}"

# ---------------------------------------------------------------- helpers

CODE_ALPHABET = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"  # no ambiguous chars

def generate_code():
    return "PAL-" + "".join(secrets.choice(CODE_ALPHABET) for _ in range(4)) + "-" + "".join(
        secrets.choice(CODE_ALPHABET) for _ in range(4)
    )

def issue_unique_code():
    conn = db()
    for _ in range(10):
        code = generate_code()
        if not conn.execute("SELECT 1 FROM gift_cards WHERE code = ?", (code,)).fetchone():
            conn.close()
            return code
    conn.close()
    raise RuntimeError("could not generate a unique gift card code")

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")

def gift_card_email_html(purchaser_name, recipient_name, code, message):
    extra = f"<p><em>\"{message}\"</em></p>" if message else ""
    return f"""\
<html><body style="font-family: Arial, sans-serif; line-height: 1.6;">
<p>Hi {recipient_name},</p>
<p>Get ready to POP into something delicious! &#x1F37F;&#x1F389;</p>
<p>I&rsquo;m excited to let you know that {purchaser_name} sent you a Pop-A-Licious gift card!
That means you&rsquo;re officially cleared for a flavor adventure!</p>
<p>With 25+ wild, wonderful, and downright delicious popcorn flavors, we&rsquo;re proving that
popcorn is so much more than butter and salt!* From sweet treats like Banana Pudding and
Birthday Cake to bold favorites like Nashville Hot and Cheddar Jalape&ntilde;o,
there&rsquo;s a flavor for every craving.</p>
<p>Your mission? Pick your favorites, grab a bag (or several!), and let the snacking begin!</p>
{extra}
<p>&#x1F381; <strong>Your Pop-A-Licious Gift Card: {code}</strong></p>
<p>&#x1F310; Explore the flavors: <a href="https://pop-a-licious.com">www.pop-a-licious.com</a></p>
<p>A huge thank-you to {purchaser_name} for sharing the popcorn love!</p>
<p>Enjoy every crunchy, sweet, savory, flavor-packed bite. Because around here, we believe
life is better when you give it a little POP!</p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>*It&rsquo;s Not Just Butter &amp; Salt!</em> &#x1F37F;</p>
</body></html>"""

def send_gift_card_email(to_email, purchaser_name, recipient_name, code, message):
    resp = requests.post(
        "https://api.resend.com/emails",
        headers={"Authorization": f"Bearer {RESEND_API_KEY}", "Content-Type": "application/json"},
        json={
            "from": EMAIL_FROM,
            "to": [to_email],
            "subject": f"{purchaser_name} sent you a Pop-A-Licious gift card!",
            "html": gift_card_email_html(purchaser_name, recipient_name, code, message),
        },
        timeout=15,
    )
    resp.raise_for_status()
    return resp.json()

# Test hook: tests assign backend._MAIL_TEST_DOUBLE to a list; send_email()
# appends to it instead of calling Resend.
_MAIL_TEST_DOUBLE = None


def send_email(to_email, subject, html):
    # Test hook: tests assign backend._MAIL_TEST_DOUBLE to a list to capture
    # outbound mail instead of calling Resend.
    if _MAIL_TEST_DOUBLE is not None:
        _MAIL_TEST_DOUBLE.append({"to": to_email, "subject": subject, "html": html})
        return {"id": "test-mail-captured"}
    resp = requests.post(
        "https://api.resend.com/emails",
        headers={"Authorization": f"Bearer {RESEND_API_KEY}", "Content-Type": "application/json"},
        json={"from": EMAIL_FROM, "to": [to_email], "subject": subject, "html": html},
        timeout=15,
    )
    resp.raise_for_status()
    return resp.json()

def send_gift_card_email(to_email, purchaser_name, recipient_name, code, message):
    return send_email(
        to_email,
        f"{purchaser_name} sent you a Pop-A-Licious gift card!",
        gift_card_email_html(purchaser_name, recipient_name, code, message),
    )

def order_email_html(name, items_summary, amount_total_cents, gift_card_code, discount_cents, promo_code=""):
    dollars = lambda c: f"${c / 100:,.2f}"
    gc_line = (
        f"<p>Gift card applied: <strong>{gift_card_code}</strong> "
        f"({dollars(discount_cents)} off)</p>"
        if gift_card_code and discount_cents
        else ""
    )
    promo_line = (
        f"<p>Promo code applied: <strong>{promo_code}</strong></p>" if promo_code else ""
    )
    return f"""\
<html><body style="font-family: Arial, sans-serif; line-height: 1.6;">
<p>Hi {name or "there"},</p>
<p>Thanks for your Pop-A-Licious order! We&rsquo;re popping it fresh for you. &#x1F37F;</p>
<p><strong>Your order:</strong> {items_summary}</p>
{gc_line}
{promo_line}
<p><strong>Total charged:</strong> {dollars(amount_total_cents)}</p>
<p>We&rsquo;ll email your tracking number as soon as it ships.</p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>
</body></html>"""

# Where new-order notifications go (merchant inbox).
ORDER_NOTIFY_EMAIL = os.environ.get("ORDER_NOTIFY_EMAIL", "orders@pop-a-licious.com")

def merchant_order_email_html(order_ref, name, email, items_summary,
                              amount_total_cents, gift_card_code,
                              discount_cents, promo_code="", shipping="",
                              label_url="", tracking_number=""):
    dollars = lambda c: f"${c / 100:,.2f}"
    rows = [
        ("Order", order_ref),
        ("Customer", html.escape(f"{name} <{email}>" if name else email)),
        ("Items", html.escape(items_summary or "—")),
        ("Total charged", dollars(amount_total_cents)),
    ]
    if gift_card_code:
        rows.append(("Gift card", f"{html.escape(gift_card_code)} (−{dollars(discount_cents)})"))
    if promo_code:
        rows.append(("Promo code", html.escape(promo_code)))
    if shipping:
        rows.append(("Ship to", html.escape(shipping)))
    if tracking_number:
        rows.append(("Tracking", html.escape(tracking_number)))
    if label_url:
        rows.append(("Shipping label",
                     f'<a href="{html.escape(label_url)}">Print shipping label (PDF)</a>'))
    body = "".join(f"<p><strong>{k}:</strong> {v}</p>" for k, v in rows)
    return (
        '<html><body style="font-family: Arial, sans-serif; line-height: 1.6;">'
        "<h2>New Pop-A-Licious order</h2>"
        f"{body}</body></html>"
    )

def notify_merchant_of_order(order_ref, name, email, items_summary,
                             amount_total_cents, gift_card_code,
                             discount_cents, promo_code="", shipping="",
                             label_url="", tracking_number=""):
    """Email the merchant about a new order. Never raises — a failed
    notification must not break order fulfillment."""
    if not ORDER_NOTIFY_EMAIL:
        return
    try:
        send_email(
            ORDER_NOTIFY_EMAIL,
            f"New order {order_ref} — ${amount_total_cents / 100:,.2f}",
            merchant_order_email_html(order_ref, name, email, items_summary,
                                      amount_total_cents, gift_card_code,
                                      discount_cents, promo_code, shipping,
                                      label_url, tracking_number),
        )
    except Exception:
        pass

# ---------------------------------------------------------------- routes

@app.get("/healthz")
def healthz():
    return jsonify(ok=DB_OK, db_error=DB_ERROR, database_path=DATABASE_PATH)

@app.get("/api/stripe/config")
def stripe_config():
    """Public Stripe publishable key for embedded checkout (Stripe.js)."""
    if not STRIPE_PUBLISHABLE_KEY:
        return jsonify(error="Stripe is not configured"), 503
    return jsonify(publishable_key=STRIPE_PUBLISHABLE_KEY)

@app.post("/api/gift-cards/checkout")
def create_checkout():
    data = request.get_json(force=True) or {}
    try:
        amount = int(data.get("amount_cents", 0))
    except (TypeError, ValueError):
        return jsonify(error="amount_cents must be an integer number of cents"), 400
    purchaser_name = (data.get("purchaser_name") or "").strip()
    purchaser_email = (data.get("purchaser_email") or "").strip()
    recipient_name = (data.get("recipient_name") or "").strip()
    recipient_email = (data.get("recipient_email") or "").strip()
    message = (data.get("message") or "").strip()[:500]
    non_refundable_ok = bool(data.get("non_refundable_ack"))

    min_allowed = 50 if (ALLOW_TEST_AMOUNTS and amount == 50) else MIN_AMOUNT_CENTS
    if not (min_allowed <= amount <= MAX_AMOUNT_CENTS):
        min_str = "$0.50" if min_allowed == 50 else f"${min_allowed // 100}"
        return jsonify(error=f"amount must be between {min_str} and ${MAX_AMOUNT_CENTS // 100}"), 400
    if not purchaser_name or not EMAIL_RE.match(purchaser_email):
        return jsonify(error="valid purchaser name and email are required"), 400
    if not recipient_name or not EMAIL_RE.match(recipient_email):
        return jsonify(error="valid recipient name and email are required"), 400
    if not non_refundable_ok:
        return jsonify(error="please acknowledge the gift card is non-refundable"), 400

    try:
        session = stripe.checkout.Session.create(
            mode="payment",
            line_items=[
                {
                    "price_data": {
                        "currency": "usd",
                        "unit_amount": amount,
                        "product": GIFT_CARD_PRODUCT_ID,
                    },
                    "quantity": 1,
                }
            ],
            customer_email=purchaser_email,
            metadata={
                "type": "gift_card",
                "purchaser_name": purchaser_name,
                "purchaser_email": purchaser_email,
                "recipient_name": recipient_name,
                "recipient_email": recipient_email,
                "message": message,
            },
            success_url=f"{SITE_URL}/#gift-card-success?session_id={{CHECKOUT_SESSION_ID}}",
            cancel_url=f"{SITE_URL}/#gift-cards",
        )
    except stripe.error.StripeError:
        return jsonify(error="the payment service could not start checkout"), 502
    return jsonify(url=session.url)

@app.post("/api/webhooks/stripe")
def stripe_webhook():
    payload = request.get_data()
    sig = request.headers.get("Stripe-Signature", "")
    try:
        event = stripe.Webhook.construct_event(payload, sig, STRIPE_WEBHOOK_SECRET)
    except Exception:
        return jsonify(error="invalid signature"), 400

    if event["type"] == "checkout.session.completed":
        session = event["data"]["object"]
        meta = session.get("metadata") or {}
        if session.get("payment_status") == "paid":
            if meta.get("type") == "gift_card":
                fulfill_gift_card(session, meta)
            elif meta.get("type") == "order":
                fulfill_order(session, meta)

    return jsonify(received=True)

def fulfill_order(session, meta):
    session_id = session["id"]
    conn = db()
    if conn.execute(
        "SELECT 1 FROM orders WHERE stripe_session_id = ?", (session_id,)
    ).fetchone():
        conn.close()
        return  # already fulfilled (idempotent)

    code = meta.get("gift_card_code", "")
    try:
        discount = int(meta.get("gift_card_discount_cents") or 0)
    except (TypeError, ValueError):
        discount = 0
    if code and discount > 0:
        cur = conn.execute(
            "UPDATE gift_cards SET balance_cents = balance_cents - ?"
            " WHERE code = ? AND balance_cents >= ?",
            (discount, code, discount),
        )
        if cur.rowcount:
            now = datetime.now(timezone.utc).isoformat()
            conn.execute(
                "INSERT INTO redemptions (code, amount_cents, order_ref, created_at) VALUES (?, ?, ?, ?)",
                (code, discount, session_id, now),
            )

    details = session.get("customer_details") or {}
    email = details.get("email") or session.get("customer_email") or ""
    name = details.get("name") or ""
    amount_total = int(session.get("amount_total") or 0)
    items_summary = meta.get("items_summary", "")
    promo = meta.get("promo_code", "")
    # Shipping address for the admin order view.
    addr = details.get("address") or {}
    ship_parts = [addr.get("line1", ""), addr.get("line2", ""), addr.get("city", ""),
                  addr.get("state", ""), addr.get("postal_code", ""), addr.get("country", "")]
    shipping_address = ", ".join(p for p in ship_parts if p)
    rcode = meta.get("reward_code", "")

    if promo and email:
        conn.execute(
            "INSERT OR IGNORE INTO promo_redemptions (code, email, stripe_session_id, created_at) VALUES (?, ?, ?, ?)",
            (promo, email, session_id, datetime.now(timezone.utc).isoformat()),
        )

    # Email first: if sending fails we raise before committing, so Stripe
    # retries the webhook and the whole fulfillment runs again cleanly.
    if email:
        send_email(
            email,
            "Your Pop-A-Licious order is confirmed!",
            order_email_html(name, items_summary, amount_total, code, discount, promo),
        )

    now = datetime.now(timezone.utc).isoformat()
    # Shippo label: create from the Stripe shipping address (never blocks the
    # order — failures leave the label fields blank for admin retry).
    try:
        total_qty = int(meta.get("total_qty") or 0)
    except (TypeError, ValueError):
        total_qty = 0
    ship = session.get("shipping_details") or {}
    ship_addr = ship.get("address") or {}
    label_url, tracking_number = _create_shippo_label(
        _shippo_address_to(
            name=ship.get("name") or name,
            street1=ship_addr.get("line1", ""),
            street2=ship_addr.get("line2", ""),
            city=ship_addr.get("city", ""),
            state=ship_addr.get("state", ""),
            zip_code=ship_addr.get("postal_code", ""),
            country=ship_addr.get("country", "US"),
        ),
        total_qty,
        order_ref=session_id,
    )
    label_created_at = now if label_url else ""
    conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, total_qty,
            shippo_label_url, shippo_tracking_number, shippo_label_created_at,
            created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (session_id, email, name, shipping_address, items_summary, amount_total,
         code, discount, promo, rcode, total_qty,
         label_url or "", tracking_number or "", label_created_at, now),
    )
    # Loyalty: mark a redeemed reward code as used (single use).
    if rcode:
        conn.execute(
            "UPDATE loyalty_rewards SET used = 1, used_at = ? WHERE code = ? AND used = 0",
            (now, rcode),
        )
    # Printful: forward any merch items to Printful for POD fulfillment.
    # Never blocks the order — failures leave the fields blank for admin retry.
    merch_items = _parse_merch_items(items_summary)
    printful_order_id, printful_error = "", ""
    if merch_items:
        pf_recipient = {
            "name": ship.get("name") or name,
            "address1": ship_addr.get("line1", ""),
            "address2": ship_addr.get("line2", ""),
            "city": ship_addr.get("city", ""),
            "state_code": ship_addr.get("state", ""),
            "country_code": ship_addr.get("country", "US"),
            "zip": ship_addr.get("postal_code", ""),
            "email": email,
        }
        pf_id, pf_err = submit_printful_order(pf_recipient, merch_items, order_ref=session_id)
        if pf_id:
            printful_order_id = str(pf_id)
            conn.execute(
                "UPDATE orders SET printful_order_id = ?, printful_status = 'submitted'"
                " WHERE stripe_session_id = ?",
                (printful_order_id, session_id),
            )
        else:
            printful_error = pf_err or "unknown error"
    # Analytics: this shopper's cart converted — not abandoned.
    if email:
        conn.execute(
            "UPDATE cart_events SET ordered = 1 WHERE email = ? AND ordered = 0",
            (email,),
        )
    # Loyalty: credit Kernels (1 per $1 of total charged) to the member's account.
    if email:
        urow = conn.execute(
            "SELECT id FROM users WHERE email = ?", (email,)
        ).fetchone()
        if urow:
            _credit_kernels(conn, urow["id"],
                            amount_total // 100 * KERNELS_PER_DOLLAR,
                            "purchase", order_ref=session_id)
    conn.commit()
    conn.close()

    ship = session.get("shipping_details") or {}
    ship_addr = ship.get("address") or {}
    shipping = ", ".join(
        x for x in [
            ship.get("name"),
            ship_addr.get("line1"), ship_addr.get("line2"),
            ship_addr.get("city"), ship_addr.get("state"),
            ship_addr.get("postal_code"), ship_addr.get("country"),
        ] if x
    )
    notify_merchant_of_order(session_id, name, email, items_summary,
                             amount_total, code, discount, promo, shipping,
                             label_url or "", tracking_number or "")

def fulfill_gift_card(session, meta):
    session_id = session["id"]
    conn = db()
    existing = conn.execute(
        "SELECT code FROM gift_cards WHERE stripe_session_id = ?", (session_id,)
    ).fetchone()
    if existing:
        conn.close()
        return existing["code"]  # already fulfilled (idempotent)

    code = issue_unique_code()
    amount = int(session.get("amount_total") or 0)
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        """INSERT INTO gift_cards
           (code, amount_cents, balance_cents, purchaser_name, purchaser_email,
            recipient_name, recipient_email, message, stripe_session_id, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (
            code, amount, amount,
            meta.get("purchaser_name", ""), meta.get("purchaser_email", ""),
            meta.get("recipient_name", ""), meta.get("recipient_email", ""),
            meta.get("message", ""), session_id, now,
        ),
    )
    conn.commit()
    conn.close()

    send_gift_card_email(
        meta["recipient_email"], meta["purchaser_name"],
        meta["recipient_name"], code, meta.get("message", ""),
    )
    return code

@app.get("/api/gift-cards/balance")
def balance():
    code = (request.args.get("code") or "").strip().upper()
    if not code:
        return jsonify(error="code is required"), 400
    conn = db()
    row = conn.execute(
        "SELECT code, balance_cents, active FROM gift_cards WHERE code = ?", (code,)
    ).fetchone()
    conn.close()
    if not row or not row["active"]:
        return jsonify(error="gift card not found"), 404
    return jsonify(code=row["code"], balance_cents=row["balance_cents"])

@app.post("/api/gift-cards/redeem")
def redeem():
    data = request.get_json(force=True) or {}
    code = (data.get("code") or "").strip().upper()
    try:
        amount = int(data.get("amount_cents", 0))
    except (TypeError, ValueError):
        return jsonify(error="amount_cents must be an integer number of cents"), 400
    order_ref = (data.get("order_ref") or "").strip()[:120]

    if not code or amount <= 0:
        return jsonify(error="code and a positive amount_cents are required"), 400

    conn = db()
    row = conn.execute(
        "SELECT code, balance_cents, active FROM gift_cards WHERE code = ?", (code,)
    ).fetchone()
    if not row or not row["active"]:
        conn.close()
        return jsonify(error="gift card not found"), 404

    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "UPDATE gift_cards SET balance_cents = balance_cents - ?"
        " WHERE code = ? AND balance_cents >= ?",
        (amount, code, amount),
    )
    if not cur.rowcount:
        conn.close()
        return jsonify(error="insufficient balance"), 402
    conn.execute(
        "INSERT INTO redemptions (code, amount_cents, order_ref, created_at) VALUES (?, ?, ?, ?)",
        (code, amount, order_ref, now),
    )
    conn.commit()
    new_balance = row["balance_cents"] - amount
    conn.close()
    return jsonify(code=code, redeemed_cents=amount, new_balance_cents=new_balance)

def _shippo_rate_options(dest_zip, total_qty, country="US"):
    """Cheapest-first Shippo rate options (USPS/UPS/FedEx).

    Returns None when Shippo is unusable (no key or request failure),
    otherwise the (possibly empty) sorted option list.
    """
    if not SHIPPO_API_KEY:
        return None
    weight_oz = max(8 * total_qty, 8)
    try:
        resp = requests.post(
            "https://api.goshippo.com/shipments/",
            headers={
                "Authorization": f"ShippoToken {SHIPPO_API_KEY}",
                "Content-Type": "application/json",
            },
            json={
                "address_from": SHIP_FROM,
                "address_to": {"zip": dest_zip, "country": country},
                "parcels": [
                    {
                        "length": "12", "width": "9", "height": "6",
                        "distance_unit": "in",
                        "weight": str(weight_oz), "mass_unit": "oz",
                    }
                ],
                "async": False,
            },
            timeout=30,
        )
        resp.raise_for_status()
    except requests.RequestException:
        return None

    rates = resp.json().get("rates") or []
    options = []
    for r in rates:
        provider = (r.get("provider") or "").lower()
        if provider not in {"usps", "ups", "fedex"}:
            continue
        try:
            cents = int(round(float(r.get("amount", 0)) * 100))
        except (TypeError, ValueError):
            continue
        svc = r.get("servicelevel") or {}
        options.append({
            "carrier": r.get("provider"),
            "service": svc.get("name") or "",
            "amount_cents": cents,
            "currency": (r.get("currency") or "USD").upper(),
        })
    options.sort(key=lambda o: o["amount_cents"])
    return options

def _cheapest_shipping_cents(dest_zip, total_qty, country="US"):
    """Cheapest Shippo rate in cents, or None when shipping is unavailable."""
    options = _shippo_rate_options(dest_zip, total_qty, country)
    if not options:
        return None
    return options[0]["amount_cents"]

def _create_shippo_label(address_to, total_qty, order_ref=""):
    """Create and purchase a Shippo shipping label.

    address_to: dict with name, street1, street2, city, state, zip, country.
    Returns (label_url, tracking_number); (None, None) on any failure.
    NEVER raises — a label failure must never break order completion.
    """
    if not SHIPPO_API_KEY:
        return None, None
    try:
        total_qty = int(total_qty or 0)
    except (TypeError, ValueError):
        total_qty = 0
    if total_qty <= 0:
        return None, None
    if not (address_to.get("zip") or "").strip():
        return None, None
    weight_oz = max(8 * total_qty, 8)
    parcel = {
        "length": "12", "width": "9", "height": "6",
        "distance_unit": "in",
        "weight": str(weight_oz), "mass_unit": "oz",
    }
    try:
        resp = requests.post(
            "https://api.goshippo.com/shipments/",
            headers={
                "Authorization": f"ShippoToken {SHIPPO_API_KEY}",
                "Content-Type": "application/json",
            },
            json={
                "address_from": SHIP_FROM,
                "address_to": address_to,
                "parcels": [parcel],
                "async": False,
            },
            timeout=30,
        )
        resp.raise_for_status()
        rates = resp.json().get("rates") or []
        best_rate_id = None
        best_cents = None
        for r in rates:
            provider = (r.get("provider") or "").lower()
            if provider not in {"usps", "ups", "fedex"}:
                continue
            try:
                cents = int(round(float(r.get("amount", 0)) * 100))
            except (TypeError, ValueError):
                continue
            if best_cents is None or cents < best_cents:
                best_cents = cents
                best_rate_id = r.get("object_id")
        if not best_rate_id:
            print(f"[shippo] no purchasable rates for order {order_ref}")
            return None, None
        tx = requests.post(
            "https://api.goshippo.com/transactions/",
            headers={
                "Authorization": f"ShippoToken {SHIPPO_API_KEY}",
                "Content-Type": "application/json",
            },
            json={"rate": best_rate_id, "label_file_type": "PDF", "async": False},
            timeout=30,
        )
        tx.raise_for_status()
        tdata = tx.json()
        if tdata.get("status") != "SUCCESS":
            print(f"[shippo] transaction not successful for order {order_ref}: "
                  f"{tdata.get('messages')}")
            return None, None
        return tdata.get("label_url"), tdata.get("tracking_number")
    except Exception as e:
        print(f"[shippo] label creation failed for order {order_ref}: {e}")
        return None, None

def _shippo_address_to(name="", street1="", street2="", city="", state="",
                       zip_code="", country="US"):
    """Build a Shippo address_to dict, dropping blank fields."""
    addr = {"country": (country or "US").strip().upper()[:2] or "US"}
    if (name or "").strip():
        addr["name"] = name.strip()
    if (street1 or "").strip():
        addr["street1"] = street1.strip()
    if (street2 or "").strip():
        addr["street2"] = street2.strip()
    if (city or "").strip():
        addr["city"] = city.strip()
    if (state or "").strip():
        addr["state"] = state.strip()
    if (zip_code or "").strip():
        addr["zip"] = zip_code.strip()
    return addr

@app.post("/api/shipping/rates")
def shipping_rates():
    """Return the cheapest USPS/UPS/FedEx rate for a cart via Shippo.

    Body: { destination_zip, country?, items: [{quantity}] }
    Parcel defaults: 8 oz per bag, 12x9x6 in box.
    """
    if not SHIPPO_API_KEY:
        return jsonify(error="shipping is not configured"), 503
    data = request.get_json(force=True) or {}
    dest_zip = (data.get("destination_zip") or "").strip()
    country = (data.get("country") or "US").strip().upper()[:2] or "US"
    try:
        total_qty = sum(int(it.get("quantity", 0)) for it in (data.get("items") or []))
    except (TypeError, ValueError):
        return jsonify(error="invalid items"), 400
    if not dest_zip:
        return jsonify(error="destination_zip is required"), 400
    if total_qty <= 0:
        return jsonify(error="cart is empty"), 400

    options = _shippo_rate_options(dest_zip, total_qty, country)
    if options is None:
        return jsonify(error="could not reach the shipping service"), 502
    if not options:
        return jsonify(error="no shipping rates found"), 502
    return jsonify(cheapest=options[0], all=options[:6])

@app.get("/api/discounts/validate")
def validate_discount():
    """Identify a discount code for the checkout discount field.

    Returns {type: 'promo', ...} for Offers-page promo codes or
    {type: 'gift_card', ...} for gift card codes; 404 when unknown.
    """
    code = (request.args.get("code") or "").strip().upper()
    if not code:
        return jsonify(error="code is required"), 400
    if code in PROMOS:
        p = PROMOS[code]
        return jsonify(type="promo", code=code, label=p["label"], description=p["description"])
    conn = db()
    row = conn.execute(
        "SELECT balance_cents, active FROM gift_cards WHERE code = ?", (code,)
    ).fetchone()
    if row and row["active"]:
        conn.close()
        return jsonify(type="gift_card", code=code, balance_cents=row["balance_cents"])
    # Loyalty reward codes (KERN-...).
    rrow = conn.execute(
        "SELECT reward_type, used FROM loyalty_rewards WHERE code = ?", (code,)
    ).fetchone()
    conn.close()
    if rrow and not rrow["used"]:
        rtype = rrow["reward_type"]
        if rtype.startswith("merch:"):
            # Merch reward: discount = the item's price (customer pays shipping only)
            _, sku, size = rtype.split(":", 2)
            prod = PRINTFUL_MERCH.get(sku, {})
            disc = prod.get("price_cents", 0)
            label = f"Free {prod.get('name', 'Merch')} ({size})"
        else:
            disc = REWARD_DISCOUNT_CENTS.get(rtype, 0)
            label = rtype.replace("_", " ").title()
        return jsonify(type="reward", code=code, label=label,
                       discount_cents=disc if isinstance(disc, int) else 0,
                       merch_sku=sku if rtype.startswith("merch:") else None,
                       merch_size=size if rtype.startswith("merch:") else None)
    return jsonify(error="code not found"), 404

# ---------------- Printful merch fulfillment ----------------
# Maps site merch SKUs to Printful catalog variant IDs + uploaded file IDs.
# SKU format: MERCH-{product}-{size} (e.g. MERCH-TEE-M, MERCH-HAT-OS).
PRINTFUL_MERCH = {
    "MERCH-TEE": {  # Big Flavor Staple Tee (Bella+Canvas 3001, Black)
        "name": "Big Flavor Staple Tee", "price_cents": 2800,
        "file_id": "1086595717", "file_type": "default",
        "variants": {"XS": 9527, "S": 4016, "M": 4017, "L": 4018, "XL": 4019,
                     "2XL": 4020, "3XL": 5295, "4XL": 5310, "5XL": 12871},
    },
    "MERCH-HOODIE": {  # Neon Nights Hoodie (Cotton Heritage M2580, Black)
        "name": "Neon Nights Hoodie", "price_cents": 5500,
        "file_id": "1086601850", "file_type": "default",
        "variants": {"XS": 53488, "S": 10779, "M": 10780, "L": 10781,
                     "XL": 10782, "2XL": 10783, "3XL": 13416, "4XL": 53493},
    },
    "MERCH-VINTAGE-TEE": {  # Vintage Crunch Tee (Comfort Colors 1717, Blue Spruce)
        "name": "Vintage Crunch Heavyweight Tee", "price_cents": 3400,
        "file_id": "1086603315", "file_type": "default",
        "variants": {"S": 17686, "M": 17687, "L": 17688, "XL": 17689,
                     "2XL": 17690, "3XL": 17691, "4XL": 17692},
    },
    "MERCH-HAT": {  # Signature Script Dad Hat (Yupoong 6245CM, Black) — embroidery
        "name": "Signature Script Dad Hat", "price_cents": 3200,
        "file_id": "1086604100", "file_type": "embroidery_front_large",
        "variants": {"OS": 7854},
    },
    "MERCH-MUG": {  # But First, Popcorn Mug (White Glossy 11oz)
        "name": "But First, Popcorn Mug", "price_cents": 1800,
        "file_id": "1086605611", "file_type": "default",
        "variants": {"11OZ": 1320},
    },
    "MERCH-TOTE": {  # Pop It Like It's Hot Eco Tote (Econscious EC8000, Oyster)
        "name": "Pop It Like It's Hot Eco Tote", "price_cents": 2800,
        "file_id": "1086609725", "file_type": "default",
        "variants": {"OS": 10458},
    },
    "MERCH-BACKPACK": {  # Kernel Chaos All-Over Backpack
        "name": "Kernel Chaos All-Over Backpack", "price_cents": 6500,
        "file_id": "1086619935", "file_type": "default",
        "variants": {"OS": 9063},
    },
    "MERCH-UTIL-BACKPACK": {  # Midnight Pop Utility Backpack (Black)
        "name": "Midnight Pop Utility Backpack", "price_cents": 7200,
        "file_id": "1086621108", "file_type": "default",
        "variants": {"OS": 24563},
    },
    "MERCH-SOCKS": {  # Popcorn Party Crew Socks
        "name": "Popcorn Party Crew Socks", "price_cents": 1600,
        "file_id": "1086613804", "file_type": "socks",
        "variants": {"S": 22786, "M": 22787, "L": 22788},
    },
    "MERCH-STICKERS": {  # Pop Pack Sticker Set (3x3)
        "name": "Pop Pack Sticker Set", "price_cents": 800,
        "file_id": "1086612480", "file_type": "default",
        "variants": {"3X3": 10163},
    },
    "MERCH-MAGSAFE": {  # Neon Nights MagSafe iPhone Case
        "name": "Neon Nights MagSafe iPhone Case", "price_cents": 3000,
        "file_id": "1086636957", "file_type": "default",
        "variants": {
            "IP14": 20687, "IP14PLUS": 20691, "IP14PRO": 20689,
            "IP14PROMAX": 20693, "IP15": 20319, "IP15PLUS": 20323,
            "IP15PRO": 20321, "IP15PROMAX": 20325, "IP16": 20327,
            "IP16PLUS": 20333, "IP16PRO": 20329, "IP16PROMAX": 20331,
            "IP17": 34001, "IP17AIR": 34003, "IP17PRO": 34005,
            "IP17PROMAX": 34007, "IP18PRO": 53188, "IP18PROMAX": 53190,
        },
    },
    "MERCH-IPHONE-CASE": {  # Big Flavor Tough iPhone Case
        "name": "Big Flavor Tough iPhone Case", "price_cents": 2800,
        "file_id": "1086637891", "file_type": "default",
        "variants": {
            "IP11": 15381, "IP11PRO": 15382, "IP11PROMAX": 15383,
            "IP12": 15384, "IP12MINI": 15385, "IP12PRO": 15386,
            "IP12PROMAX": 15387, "IP13": 15388, "IP13MINI": 15389,
            "IP13PRO": 15390, "IP13PROMAX": 15391, "IP14": 16124,
            "IP14PLUS": 16128, "IP14PRO": 16126, "IP14PROMAX": 16130,
            "IP15": 17714, "IP15PLUS": 17716, "IP15PRO": 17718,
            "IP15PROMAX": 17720, "IP16": 20302, "IP16PLUS": 20303,
            "IP16PRO": 20304, "IP16PROMAX": 20305, "IP17": 33985,
            "IP17AIR": 33986, "IP17PRO": 33987, "IP17PROMAX": 33988,
            "IP18PRO": 52384, "IP18PROMAX": 52386,
        },
    },
    "MERCH-SAMSUNG-CASE": {  # But First, Popcorn Tough Samsung Case
        "name": "But First, Popcorn Tough Samsung Case", "price_cents": 2800,
        "file_id": "1086638309", "file_type": "default",
        "variants": {
            "S20": 16981, "S20FE": 16975, "S20PLUS": 16977,
            "S20ULTRA": 16979, "S21": 16989, "S21FE": 16983,
            "S21PLUS": 16985, "S21ULTRA": 16987, "S22": 16995,
            "S22PLUS": 16991, "S22ULTRA": 16993, "S23": 17001,
            "S23PLUS": 16997, "S23ULTRA": 16999, "S24": 18743,
            "S24PLUS": 18744, "S24ULTRA": 18745, "S25": 21469,
            "S25PLUS": 21471, "S25ULTRA": 21473, "S26": 49327,
            "S26PLUS": 49328, "S26ULTRA": 49329,
        },
    },
    # Shoe file IDs verified from the Printful dashboard.
    "MERCH-HIGHTOP-M": {  # Neon Nights Men's High-Top Canvas Shoes
        "name": "Neon Nights Men's High-Top Canvas Shoes", "price_cents": 7500,
        "file_id": "1086642392", "file_type": "default",
        "variants": {
            "5": 17450, "6": 17452, "7": 17454, "8": 17456,
            "9": 17458, "10": 17460, "11": 17462, "12": 17464,
            "13": 17466, "55": 17451, "65": 17453, "75": 17455,
            "85": 17457, "95": 17459, "105": 17461, "115": 17463,
            "125": 17465,
        },
    },
    "MERCH-HIGHTOP-W": {  # Neon Nights Women's High-Top Canvas Shoes
        "name": "Neon Nights Women's High-Top Canvas Shoes", "price_cents": 7500,
        "file_id": "1086642392", "file_type": "default",
        "variants": {
            "5": 17467, "6": 17469, "7": 17470, "8": 17473,
            "9": 17475, "10": 17477, "11": 17479, "12": 17481,
            "55": 17468, "65": 17471, "75": 17472, "85": 17474,
            "95": 17476, "105": 17478, "115": 17480,
        },
    },
    "MERCH-SLIPON-M": {  # Popcorn Party Men's Slip-On Canvas Shoes
        "name": "Popcorn Party Men's Slip-On Canvas Shoes", "price_cents": 6800,
        "file_id": "1086613804", "file_type": "default",
        "variants": {
            "5": 14736, "6": 14738, "7": 14740, "8": 14742,
            "9": 14744, "10": 14746, "11": 14748, "12": 14750,
            "13": 14752, "55": 14737, "65": 14739, "75": 14741,
            "85": 14743, "95": 14745, "105": 14747, "115": 14749,
            "125": 14751,
        },
    },
    "MERCH-SLIPON-W": {  # Popcorn Party Women's Slip-On Canvas Shoes
        "name": "Popcorn Party Women's Slip-On Canvas Shoes", "price_cents": 6800,
        "file_id": "1086613804", "file_type": "default",
        "variants": {
            "5": 14721, "6": 14723, "7": 14725, "8": 14727,
            "9": 14729, "10": 14731, "11": 14733, "12": 14735,
            "55": 14722, "65": 14724, "75": 14726, "85": 14728,
            "95": 14730, "105": 14732, "115": 14734,
        },
    },
    "MERCH-LACEUP-M": {  # Neon Nights Men's Lace-Up Canvas Shoes
        "name": "Neon Nights Men's Lace-Up Canvas Shoes", "price_cents": 7000,
        "file_id": "1086649031", "file_type": "default",
        "variants": {
            "5": 20920, "6": 20922, "7": 20924, "8": 20926,
            "9": 20928, "10": 20930, "11": 20932, "12": 20934,
            "13": 20936, "55": 20921, "65": 20923, "75": 20925,
            "85": 20927, "95": 20929, "105": 20931, "115": 20933,
            "125": 20935,
        },
    },
    "MERCH-LACEUP-W": {  # Neon Nights Women's Lace-Up Canvas Shoes
        "name": "Neon Nights Women's Lace-Up Canvas Shoes", "price_cents": 7000,
        "file_id": "1086649031", "file_type": "default",
        "variants": {
            "5": 20937, "6": 20939, "7": 20941, "8": 20943,
            "9": 20945, "10": 20947, "11": 20949, "12": 20951,
            "55": 20938, "65": 20940, "75": 20942, "85": 20944,
            "95": 20946, "105": 20948, "115": 20950,
        },
    },
    "MERCH-STRAW-TUMBLER": {  # Insulated Tumbler with Straw (20 oz)
        "name": "Pop-A-Licious Insulated Straw Tumbler", "price_cents": 3200,
        "file_id": "1086601850", "file_type": "default",
        "variants": {"BLACK": 19107, "MINT": 19108, "NAVY": 19109,
                     "PINK": 19110, "WHITE": 19111},
    },
    "MERCH-STEEL-TUMBLER": {  # Tapered Stainless Steel Tumbler (20 oz)
        "name": "Big Flavor Steel Tumbler", "price_cents": 3500,
        "file_id": "1086692382", "file_type": "default",
        "variants": {"WHITE": 23470},
    },
    "MERCH-XMAS-TUMBLER": {  # Merry Popmas Tumbler (Christmas 2026)
        "name": "Merry Popmas Tumbler", "price_cents": 3500,
        "file_id": "1086696410", "file_type": "default",
        "variants": {"WHITE": 23470},
    },
}


def _printful_headers():
    return {"Authorization": f"Bearer {PRINTFUL_API_KEY}"}


def submit_printful_order(recipient, merch_items, order_ref=""):
    """Submit merch items to Printful. Returns (printful_order_id, error).

    recipient: dict with name, address1, address2, city, state_code,
               country_code, zip, email, phone (optional).
    merch_items: list of (sku_base, size, quantity), e.g.
                 ("MERCH-TEE", "M", 2).
    """
    if not PRINTFUL_API_KEY:
        return None, "PRINTFUL_API_KEY not set"
    items = []
    for sku_base, size, qty in merch_items:
        prod = PRINTFUL_MERCH.get(sku_base)
        if not prod:
            return None, f"unknown merch SKU {sku_base}"
        variant_id = prod["variants"].get(size)
        if not variant_id:
            return None, f"unknown size {size} for {sku_base}"
        items.append({
            "variant_id": variant_id,
            "quantity": int(qty) or 1,
            "files": [{"id": prod["file_id"], "type": prod["file_type"]}],
        })
    if not items:
        return None, "no merch items"
    payload = {
        "external_id": order_ref or None,
        "recipient": {
            "name": recipient.get("name", ""),
            "address1": recipient.get("address1", ""),
            "address2": recipient.get("address2", ""),
            "city": recipient.get("city", ""),
            "state_code": recipient.get("state_code", ""),
            "country_code": recipient.get("country_code", "US"),
            "zip": recipient.get("zip", ""),
            "email": recipient.get("email", ""),
            "phone": recipient.get("phone", ""),
        },
        "items": items,
    }
    try:
        r = requests.post("https://api.printful.com/orders",
                          headers=_printful_headers(), json=payload, timeout=30)
        data = r.json()
    except Exception as e:
        return None, f"printful request failed: {e}"
    if r.status_code not in (200, 201):
        return None, f"printful error {r.status_code}: {str(data)[:300]}"
    result = data.get("result") or {}
    return result.get("id"), None


def _parse_merch_items(items_summary):
    """Extract merch (sku_base, size, qty) triples from the order items summary.

    The site cart encodes merch SKUs in the product name as MERCH-{product}-{size}.
    The summary format is "{qty}x {name}" (e.g. "2x MERCH-TEE-M Big Flavor Tee (M)").
    Returns a list of (sku_base, size, qty).
    """
    found = []
    if not items_summary:
        return found
    # Match longest SKU bases first so MERCH-VINTAGE-TEE wins over MERCH-TEE.
    bases = sorted(PRINTFUL_MERCH.keys(), key=len, reverse=True)
    for chunk in re.split(r"[;\n,]", items_summary):
        # Find qty prefix like "2x " at the start of the chunk.
        qm = re.match(r"\s*(\d+)\s*[x×]\s*", chunk)
        qty = int(qm.group(1)) if qm else 1
        for base in bases:
            m = re.search(re.escape(base) + r"-([A-Z0-9]+)\b", chunk)
            if m:
                size = m.group(1)
                if size in PRINTFUL_MERCH[base]["variants"]:
                    found.append((base, size, qty))
                break
    return found


@app.route("/api/printful/webhook", methods=["POST"])
def printful_webhook():
    data = request.get_json(force=True, silent=True) or {}
    event_type = data.get("type", "")
    payload = data.get("data") or {}
    order_info = payload.get("order") or {}
    pf_id = order_info.get("id") or payload.get("id")
    if not pf_id:
        return jsonify(ok=False, error="no order id"), 400
    conn = db()
    try:
        if event_type == "package_shipped":
            shipment = payload.get("shipment") or {}
            tracking = shipment.get("tracking_number", "")
            carrier = shipment.get("carrier", "")
            conn.execute(
                "UPDATE orders SET printful_tracking = ?, printful_carrier = ?,"
                " printful_status = 'shipped' WHERE printful_order_id = ?",
                (tracking, carrier, str(pf_id)),
            )
            # Email the customer their merch tracking number.
            row = conn.execute(
                "SELECT email, customer_name FROM orders WHERE printful_order_id = ?",
                (str(pf_id),),
            ).fetchone()
            if row and row["email"] and tracking:
                send_email(
                    row["email"],
                    "Your Pop-A-Licious merch has shipped! 📦",
                    f"<p>Hi {html.escape(row['customer_name'] or 'there')},</p>"
                    f"<p>Your merch order is on its way via {html.escape(carrier or 'carrier')}.</p>"
                    f"<p><strong>Tracking:</strong> {html.escape(tracking)}</p>"
                    "<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>",
                )
        else:
            status = event_type.replace("order_", "") or event_type
            conn.execute(
                "UPDATE orders SET printful_status = ? WHERE printful_order_id = ?",
                (status, str(pf_id)),
            )
        conn.commit()
    finally:
        conn.close()
    return jsonify(ok=True)


@app.get("/api/merch/catalog")
def merch_catalog():
    """Public merch catalog for the site shop (name, price, sizes)."""
    items = []
    for sku, prod in PRINTFUL_MERCH.items():
        items.append({
            "sku": sku,
            "name": prod["name"],
            "price_cents": prod["price_cents"],
            "sizes": sorted(prod["variants"].keys()),
        })
    return jsonify(items=items)


# Merch loyalty rewards — specific items only, each with its own kernel cost.
# Customer gets a MCH- code for free merch (pays Printful shipping only).
# Employee redemptions notify admins with a Printful link.
MERCH_REWARDS = [
    {"sku": "MERCH-STICKERS", "kernels": 300},
    {"sku": "MERCH-MUG", "kernels": 400},
    {"sku": "MERCH-TEE", "kernels": 500},
    {"sku": "MERCH-STRAW-TUMBLER", "kernels": 600},
    {"sku": "MERCH-STEEL-TUMBLER", "kernels": 700},
    {"sku": "MERCH-HOODIE", "kernels": 900},
]

# Employee merch pricing — same items, lower kernel costs.
STAFF_MERCH_REWARDS = [
    {"sku": "MERCH-STICKERS", "kernels": 100},
    {"sku": "MERCH-MUG", "kernels": 200},
    {"sku": "MERCH-TEE", "kernels": 300},
    {"sku": "MERCH-STRAW-TUMBLER", "kernels": 400},
    {"sku": "MERCH-STEEL-TUMBLER", "kernels": 500},
    {"sku": "MERCH-HOODIE", "kernels": 600},
]


def merch_rewards_for_balance(kernel_balance):
    """Return list of {kernels, sku, name, price_cents, sizes}
    for merch rewards the balance unlocks, ordered by kernel cost."""
    eligible = []
    for reward in MERCH_REWARDS:
        if kernel_balance < reward["kernels"]:
            continue
        prod = PRINTFUL_MERCH.get(reward["sku"])
        if not prod:
            continue
        eligible.append({
            "kernels": reward["kernels"],
            "sku": reward["sku"],
            "name": prod["name"],
            "price_cents": prod["price_cents"],
            "sizes": sorted(prod["variants"].keys()),
        })
    eligible.sort(key=lambda x: x["kernels"])
    return eligible


def merch_reward_for_sku(sku, kernel_balance):
    """Find the merch reward for a SKU if the balance covers it, else None."""
    for reward in MERCH_REWARDS:
        if reward["sku"] == sku and kernel_balance >= reward["kernels"]:
            return reward
    return None


def staff_merch_reward_for_sku(sku, kernel_balance):
    """Find the staff merch reward for a SKU if the balance covers it, else None."""
    for reward in STAFF_MERCH_REWARDS:
        if reward["sku"] == sku and kernel_balance >= reward["kernels"]:
            return reward
    return None


def _new_merch_code():
    return "MCH-" + secrets.token_hex(4).upper()


def _merch_template_id(sku):
    """Map SKU to Printful template ID for the admin order link."""
    return {
        "MERCH-TEE": "108855676", "MERCH-HOODIE": "108855917",
        "MERCH-VINTAGE-TEE": "108855976", "MERCH-HAT": "108856083",
        "MERCH-MUG": "108856325", "MERCH-TOTE": "108856420",
        "MERCH-BACKPACK": "108856811", "MERCH-UTIL-BACKPACK": "108856913",
        "MERCH-SOCKS": "108856731", "MERCH-STICKERS": "108856645",
        "MERCH-MAGSAFE": "108858113", "MERCH-IPHONE-CASE": "108858228",
        "MERCH-SAMSUNG-CASE": "108858203",
        "MERCH-HIGHTOP-M": "108858519", "MERCH-HIGHTOP-W": "108858565",
        "MERCH-SLIPON-M": "108858466", "MERCH-SLIPON-W": "108858622",
        "MERCH-STRAW-TUMBLER": "108861051", "MERCH-STEEL-TUMBLER": "108861085",
        "MERCH-XMAS-TUMBLER": "108861512",
    }.get(sku)


@app.get("/api/loyalty/merch-rewards")
def loyalty_merch_rewards():
    """List merch rewards available for the logged-in customer's kernel balance."""
    auth = request.headers.get("Authorization", "")
    token = auth[7:] if auth.lower().startswith("bearer ") else None
    user = _auth_user_from_token(token or _session_token_from_request())
    if not user:
        return jsonify(error="login required"), 401
    with _db() as conn:
        balance = _kernel_balance(conn, user["id"])
    return jsonify(rewards=merch_rewards_for_balance(balance), balance=balance)


@app.post("/api/loyalty/redeem-merch")
def loyalty_redeem_merch():
    """Customer redeems kernels for a merch promo code (free item, pays shipping)."""
    auth = request.headers.get("Authorization", "")
    token = auth[7:] if auth.lower().startswith("bearer ") else None
    user = _auth_user_from_token(token or _session_token_from_request())
    if not user:
        return jsonify(error="login required"), 401
    data = request.get_json(force=True, silent=True) or {}
    sku = data.get("sku", "")
    size = data.get("size", "")
    prod = PRINTFUL_MERCH.get(sku)
    if not prod or size not in prod["variants"]:
        return jsonify(error="invalid merch selection"), 400
    with _db() as conn:
        balance = _kernel_balance(conn, user["id"])
    reward = staff_merch_reward_for_sku(sku, balance)
    if not reward:
        return jsonify(error="not enough kernels for this item"), 400
    code = _new_merch_code()
    now = _now_iso()
    with _db() as conn:
        conn.execute(
            "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent, created_at)"
            " VALUES (?, ?, ?, ?, ?)",
            (user["id"], f"merch:{sku}:{size}", code, reward["kernels"], now),
        )
        _add_kernels(conn, user["id"], -reward["kernels"], f"Redeemed merch: {prod['name']} ({size})")
    return jsonify(code=code, kernels_spent=reward["kernels"],
                   item=f"{prod['name']} ({size})")


@app.post("/api/staff/redeem-merch")
def staff_redeem_merch():
    """Employee redeems kernels for merch. Deducts kernels, emails admins
    with a Printful link to manually place the order."""
    staff, err = _require_staff()
    if err:
        return err
    data = request.get_json(force=True, silent=True) or {}
    sku = data.get("sku", "")
    size = data.get("size", "")
    prod = PRINTFUL_MERCH.get(sku)
    if not prod or size not in prod["variants"]:
        return jsonify(error="invalid merch selection"), 400
    with _db() as conn:
        row = conn.execute("SELECT kernels FROM staff WHERE id = ?", (staff["id"],)).fetchone()
        balance = row["kernels"] if row else 0
    reward = staff_merch_reward_for_sku(sku, balance)
    if not reward:
        return jsonify(error="not enough kernels for this item"), 400
    now = _now_iso()
    with _db() as conn:
        conn.execute(
            "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent, staff_id, created_at)"
            " VALUES (?, ?, ?, ?, ?, ?)",
            (0, f"merch:{sku}:{size}", "STAFF-" + secrets.token_hex(4).upper(),
             reward["kernels"], staff["id"], now),
        )
        _credit_staff_kernels(conn, staff["id"], -reward["kernels"],
                           f"Redeemed merch: {prod['name']} ({size})")
    template_id = _merch_template_id(sku)
    printful_url = (f"https://www.printful.com/dashboard/stores/18907610/products/templates/{template_id}"
                    if template_id else "https://www.printful.com/dashboard")
    try:
        for admin_email in ADMIN_EMAILS:
            send_email(
                admin_email,
                f"Employee merch redemption: {staff['name']}",
                f"<p><b>{staff['name']}</b> ({staff['email']}) redeemed "
                f"<b>{prod['name']} ({size})</b> for {reward['kernels']} kernels.</p>"
                f"<p>Place the order in Printful:<br>"
                f"<a href='{printful_url}'>{printful_url}</a></p>"
                f"<p>Ship to the employee's address on file.</p>",
            )
    except Exception:
        pass
    return jsonify(ok=True, kernels_spent=reward["kernels"],
                   item=f"{prod['name']} ({size})",
                   message="Kernels deducted. Admins have been notified to place your order.")
    """Public merch catalog for the site shop (name, price, sizes)."""
    items = []
    for sku, prod in PRINTFUL_MERCH.items():
        items.append({
            "sku": sku,
            "name": prod["name"],
            "price_cents": prod["price_cents"],
            "sizes": sorted(prod["variants"].keys(),
                            key=lambda s: ({"XS": 0, "S": 1, "M": 2, "L": 3, "XL": 4,
                                            "2XL": 5, "3XL": 6, "4XL": 7, "5XL": 8,
                                            "OS": 9, "11OZ": 10, "3X3": 11}.get(s, 99), s)),
        })
    return jsonify(items=items)


@app.post("/api/printful/shipping-rates")
def printful_shipping_rates():
    """Quote Printful's actual shipping for merch items at checkout.

    Request: {recipient: {address1, city, state_code, country_code, zip},
              items: [{sku, size, quantity}]}
    Returns: {rates: [{id, name, rate_cents, ...}], cheapest_cents}
    """
    data = request.get_json(force=True, silent=True) or {}
    recipient = data.get("recipient") or {}
    req_items = data.get("items") or []
    if not PRINTFUL_API_KEY:
        return jsonify(error="merch shipping unavailable"), 503
    pf_items = []
    for it in req_items:
        sku = it.get("sku", "")
        size = it.get("size", "")
        qty = int(it.get("quantity") or 1)
        prod = PRINTFUL_MERCH.get(sku)
        if not prod:
            continue
        variant_id = prod["variants"].get(size)
        if not variant_id:
            continue
        pf_items.append({"variant_id": variant_id, "quantity": qty})
    if not pf_items:
        return jsonify(error="no valid merch items"), 400
    try:
        r = requests.post(
            "https://api.printful.com/shipping/rates",
            headers=_printful_headers(),
            json={
                "store_id": int(os.environ.get("PRINTFUL_STORE_ID", "18907610")),
                "recipient": {
                    "address1": recipient.get("address1", ""),
                    "city": recipient.get("city", ""),
                    "country_code": recipient.get("country_code", "US"),
                    "state_code": recipient.get("state_code", ""),
                    "zip": recipient.get("zip", ""),
                },
                "items": pf_items,
            },
            timeout=20,
        )
        resp = r.json()
    except Exception as e:
        return jsonify(error=f"printful rates failed: {e}"), 502
    if r.status_code != 200:
        return jsonify(error=f"printful error {r.status_code}"), 502
    rates = []
    for rate in (resp.get("result") or []):
        try:
            cents = int(float(rate.get("rate", 0)) * 100)
        except (TypeError, ValueError):
            continue
        rates.append({
            "id": rate.get("id", ""),
            "name": rate.get("name", ""),
            "rate_cents": cents,
            "currency": rate.get("currency", "USD"),
        })
    rates.sort(key=lambda x: x["rate_cents"])
    cheapest = rates[0]["rate_cents"] if rates else 0
    return jsonify(rates=rates, cheapest_cents=cheapest)


# ---------------------------------------------------------------- paypal

PAYPAL_CLIENT_ID = os.environ.get("PAYPAL_CLIENT_ID", "")
PAYPAL_CLIENT_SECRET = os.environ.get("PAYPAL_CLIENT_SECRET", "")
PAYPAL_BASE = (
    "https://api-m.sandbox.paypal.com"
    if os.environ.get("PAYPAL_MODE", "live") == "sandbox"
    else "https://api-m.paypal.com"
)

_paypal_token_cache = {"token": None, "expires_at": 0.0}

def paypal_token():
    import time
    now = time.time()
    if _paypal_token_cache["token"] and _paypal_token_cache["expires_at"] > now + 60:
        return _paypal_token_cache["token"]
    if not PAYPAL_CLIENT_ID or not PAYPAL_CLIENT_SECRET:
        raise RuntimeError("PayPal is not configured")
    resp = requests.post(
        f"{PAYPAL_BASE}/v1/oauth2/token",
        auth=(PAYPAL_CLIENT_ID, PAYPAL_CLIENT_SECRET),
        data={"grant_type": "client_credentials"},
        headers={"Accept": "application/json"},
        timeout=20,
    )
    resp.raise_for_status()
    body = resp.json()
    _paypal_token_cache["token"] = body["access_token"]
    _paypal_token_cache["expires_at"] = now + int(body.get("expires_in", 30000))
    return body["access_token"]

def paypal_api(method, path, json_body=None):
    token = paypal_token()
    resp = requests.request(
        method,
        f"{PAYPAL_BASE}{path}",
        headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
        json=json_body,
        timeout=30,
    )
    resp.raise_for_status()
    return resp.json()

def _dollars(cents):
    return f"{cents / 100:.2f}"

# ---------------------------------------------------------------- shared order math

def _compute_order(data):
    """Validate a cart + discount code; shared by the Stripe and PayPal checkouts.

    Returns (order, None) on success, or (None, (response, status)) on error.
    order keys: items, merchandise_total, email, shipping_cents, shipping_label,
    discount_kind (None|'promo'|'gift_card'), promo_code, promo_label,
    promo_percent_off, gift_card_code, gift_card_discount_cents, summary.
    """
    raw_items = data.get("items") or []
    email = (data.get("email") or "").strip()
    discount_code = (data.get("discount_code") or "").strip().upper()
    gift_card_code = (data.get("gift_card_code") or "").strip().upper()
    if discount_code and gift_card_code and discount_code != gift_card_code:
        return None, (jsonify(error="only one discount can be used per order"), 400)
    code = discount_code or gift_card_code

    items = []
    total = 0
    for it in raw_items:
        if not isinstance(it, dict):
            return None, (jsonify(error="invalid items"), 400)
        try:
            qty = int(it.get("quantity", 0))
            amt = int(it.get("amount_cents", 0))
        except (TypeError, ValueError):
            return None, (jsonify(error="invalid items"), 400)
        name = (it.get("name") or "").strip()[:120]
        if not name or qty <= 0 or amt <= 0 or qty > 99 or amt > 100000:
            return None, (jsonify(error="invalid items"), 400)
        items.append({"name": name, "amount_cents": amt, "quantity": qty})
        total += amt * qty
    if not items:
        return None, (jsonify(error="cart is empty"), 400)
    if email and not EMAIL_RE.match(email):
        return None, (jsonify(error="invalid email"), 400)
    try:
        shipping_cents = int(data.get("shipping_cents") or 0)
        merch_shipping_cents = int(data.get("merch_shipping_cents") or 0)
    except (TypeError, ValueError):
        return None, (jsonify(error="invalid shipping"), 400)
    shipping_label = (data.get("shipping_label") or "").strip()[:120]
    if shipping_cents < 0 or shipping_cents > 100000:
        return None, (jsonify(error="invalid shipping"), 400)
    if merch_shipping_cents < 0 or merch_shipping_cents > 100000:
        return None, (jsonify(error="invalid merch shipping"), 400)

    order = {
        "items": items,
        "merchandise_total": total,
        "email": email,
        "shipping_cents": shipping_cents,
        "merch_shipping_cents": merch_shipping_cents,
        "shipping_label": shipping_label,
        "discount_kind": None,
        "promo_code": "",
        "promo_label": "",
        "promo_percent_off": 0,
        "gift_card_code": "",
        "gift_card_discount_cents": 0,
        "reward_code": "",
        "reward_type": "",
        "reward_discount_cents": 0,
    }
    if code and code in PROMOS:
        # Offers-page promo code: one use per email address, one per order.
        if not email:
            return None, (jsonify(error="an email address is required to use a promo code"), 400)
        conn = db()
        used = conn.execute(
            "SELECT 1 FROM promo_redemptions WHERE code = ? AND email = ?", (code, email)
        ).fetchone()
        conn.close()
        if used:
            return None, (jsonify(error="this code has already been used"), 400)
        promo = PROMOS[code]
        order["discount_kind"] = "promo"
        order["promo_code"] = code
        order["promo_label"] = promo["description"]
        if promo["type"] == "percent":
            order["promo_percent_off"] = promo["percent_off"]
        elif promo["type"] == "free_shipping":
            if total < promo["min_subtotal_cents"]:
                return None, (jsonify(error="free shipping needs a $50+ order"), 400)
            order["shipping_cents"] = 0
            order["shipping_label"] = f"FREE ({code})"
    elif code:
        conn = db()
        reward = conn.execute(
            "SELECT reward_type FROM loyalty_rewards WHERE code = ? AND used = 0",
            (code,),
        ).fetchone()
        if reward:
            # Loyalty reward code (single use, issued from Kernels redemption).
            order["discount_kind"] = "reward"
            order["reward_code"] = code
            order["reward_type"] = reward["reward_type"]
            if reward["reward_type"] == "free_shipping":
                order["shipping_cents"] = 0
                order["shipping_label"] = f"FREE ({code})"
            elif reward["reward_type"].startswith("merch:"):
                _, sku, size = reward["reward_type"].split(":", 2)
                prod = PRINTFUL_MERCH.get(sku, {})
                order["reward_discount_cents"] = prod.get("price_cents", 0)
                order["reward_merch_sku"] = sku
                order["reward_merch_size"] = size
            else:
                order["reward_discount_cents"] = REWARD_DISCOUNT_CENTS.get(
                    reward["reward_type"], 0)
            conn.close()
        else:
            row = conn.execute(
                "SELECT balance_cents, active FROM gift_cards WHERE code = ?", (code,)
            ).fetchone()
            conn.close()
            if not row or not row["active"]:
                return None, (jsonify(error="gift card not found"), 404)
            if row["balance_cents"] <= 0:
                return None, (jsonify(error="gift card has no balance"), 402)
            order["discount_kind"] = "gift_card"
            order["gift_card_code"] = code
            order["gift_card_discount_cents"] = min(row["balance_cents"], total)

    summary = ", ".join(f"{it['quantity']}x {it['name']}" for it in items)
    if order["shipping_cents"] > 0:
        summary += f", Shipping{f' ({order['shipping_label']})' if order['shipping_label'] else ''}"
    order["summary"] = summary[:400]
    return order, None

@app.post("/api/orders/checkout")
def create_order_checkout():
    """Create a Stripe Checkout Session for a popcorn order (the store's checkout).

    Body: { items: [{name, amount_cents, quantity}], email?, discount_code?,
            shipping_cents?, shipping_label? }
    A discount code (promo or gift card) is applied as a one-time Stripe coupon;
    balances are only deducted in the webhook after successful payment.
    """
    data = request.get_json(force=True) or {}
    order, err = _compute_order(data)
    if err:
        return err[0], err[1]
    mark_abandoned_converted(data.get("email"))

    discounts = []
    try:
        if order["discount_kind"] == "promo" and order["promo_percent_off"]:
            coupon = stripe.Coupon.create(
                percent_off=order["promo_percent_off"],
                duration="once",
                max_redemptions=1,
                redeem_by=int(datetime.now(timezone.utc).timestamp()) + 86400,
                metadata={"promo_code": order["promo_code"]},
            )
            discounts = [{"coupon": coupon.id}]
        elif order["discount_kind"] == "gift_card":
            coupon = stripe.Coupon.create(
                amount_off=order["gift_card_discount_cents"],
                currency="usd",
                duration="once",
                max_redemptions=1,
                redeem_by=int(datetime.now(timezone.utc).timestamp()) + 86400,
                metadata={"gift_card_code": order["gift_card_code"]},
            )
            discounts = [{"coupon": coupon.id}]
        elif order["discount_kind"] == "reward" and order["reward_discount_cents"]:
            coupon = stripe.Coupon.create(
                amount_off=order["reward_discount_cents"],
                currency="usd",
                duration="once",
                max_redemptions=1,
                redeem_by=int(datetime.now(timezone.utc).timestamp()) + 86400,
                metadata={"reward_code": order["reward_code"]},
            )
            discounts = [{"coupon": coupon.id}]
    except stripe.error.StripeError as e:
        return jsonify(error=_stripe_error_message(e)), 502

    line_items = [
        {
            "price_data": {
                "currency": "usd",
                "unit_amount": it["amount_cents"],
                "product_data": {"name": it["name"]},
            },
            "quantity": it["quantity"],
        }
        for it in order["items"]
    ]
    if order["shipping_cents"] > 0:
        line_items.append(
            {
                "price_data": {
                    "currency": "usd",
                    "unit_amount": order["shipping_cents"],
                    "product_data": {
                        "name": f"Shipping{f' ({order['shipping_label']})' if order['shipping_label'] else ''}"
                    },
                },
                "quantity": 1,
            }
        )
    if order.get("merch_shipping_cents", 0) > 0:
        line_items.append(
            {
                "price_data": {
                    "currency": "usd",
                    "unit_amount": order["merch_shipping_cents"],
                    "product_data": {"name": "Merch shipping (Printful)"},
                },
                "quantity": 1,
            }
        )
    try:
        # Embedded checkout: the payment form renders inside our checkout page,
        # so customers never leave the site (no redirect to stripe.com).
        session = stripe.checkout.Session.create(
            mode="payment",
            ui_mode="embedded",
            line_items=line_items,
            discounts=discounts,
            # A backend-applied discount means the Stripe promo-code box stays off
            # so discounts can never be combined.
            allow_promotion_codes=not (order["gift_card_code"] or order["promo_code"]
                                       or order["reward_code"]),
            customer_email=order["email"] or None,
            shipping_address_collection={"allowed_countries": ["US"]},
            phone_number_collection={"enabled": True},
            metadata={
                "type": "order",
                "items_summary": order["summary"],
                "total_qty": str(sum(it["quantity"] for it in order["items"])),
                "gift_card_code": order["gift_card_code"],
                "gift_card_discount_cents": str(order["gift_card_discount_cents"]),
                "promo_code": order["promo_code"],
                "reward_code": order["reward_code"],
            },
            return_url=f"{SITE_URL}/#order-success?session_id={{CHECKOUT_SESSION_ID}}",
        )
    except stripe.error.StripeError:
        return jsonify(error="the payment service could not start checkout"), 502
    return jsonify(client_secret=session.client_secret, gift_card_discount_cents=order["gift_card_discount_cents"])

# ---------------------------------------------------------------- paypal checkout

@app.get("/api/paypal/config")
def paypal_config():
    """Public PayPal client ID for the checkout page's PayPal button."""
    if not PAYPAL_CLIENT_ID:
        return jsonify(error="PayPal is not configured"), 503
    return jsonify(client_id=PAYPAL_CLIENT_ID)

@app.post("/api/paypal/create-order")
def paypal_create_order():
    """Create a PayPal order for the store checkout. Body matches /api/orders/checkout."""
    data = request.get_json(force=True) or {}
    order, err = _compute_order(data)
    if err:
        return err[0], err[1]
    mark_abandoned_converted(data.get("email"))

    merch = order["merchandise_total"]
    ship = order["shipping_cents"]
    if order["discount_kind"] == "promo" and order["promo_percent_off"]:
        disc = round((merch + ship) * order["promo_percent_off"] / 100)
    elif order["discount_kind"] == "gift_card":
        disc = order["gift_card_discount_cents"]
    elif order["discount_kind"] == "reward":
        disc = order["reward_discount_cents"]
    else:
        disc = 0
    grand = max(merch + ship - disc, 0)

    pp_items = [
        {
            "name": it["name"][:127],
            "unit_amount": {"currency_code": "USD", "value": _dollars(it["amount_cents"])},
            "quantity": str(it["quantity"]),
        }
        for it in order["items"]
    ]
    if ship > 0:
        pp_items.append(
            {
                "name": f"Shipping{f' ({order['shipping_label']})' if order['shipping_label'] else ''}"[:127],
                "unit_amount": {"currency_code": "USD", "value": _dollars(ship)},
                "quantity": "1",
            }
        )

    try:
        pp = paypal_api(
            "POST",
            "/v2/checkout/orders",
            {
                "intent": "CAPTURE",
                "purchase_units": [
                    {
                        "amount": {
                            "currency_code": "USD",
                            "value": _dollars(grand),
                            "breakdown": {
                                "item_total": {
                                    "currency_code": "USD",
                                    "value": _dollars(merch + ship),
                                },
                                "discount": {
                                    "currency_code": "USD",
                                    "value": _dollars(disc),
                                },
                            },
                        },
                        "items": pp_items,
                    }
                ],
            },
        )
    except Exception:
        return jsonify(error="could not start PayPal checkout"), 502

    conn = db()
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        """INSERT INTO paypal_orders
           (paypal_order_id, email, items_summary, gift_card_code,
            gift_card_discount_cents, promo_code, reward_code, amount_total_cents,
            total_qty, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (
            pp["id"], order["email"], order["summary"], order["gift_card_code"],
            order["gift_card_discount_cents"], order["promo_code"], order["reward_code"], grand,
            sum(it["quantity"] for it in order["items"]),
            "created", now,
        ),
    )
    conn.commit()
    conn.close()
    return jsonify(id=pp["id"])

@app.post("/api/paypal/capture-order")
def paypal_capture_order():
    """Capture an approved PayPal order and fulfill it (deduct gift card,
    record promo use, save the order, email the customer)."""
    data = request.get_json(force=True) or {}
    order_id = (data.get("order_id") or "").strip()
    if not order_id:
        return jsonify(error="order_id is required"), 400

    conn = db()
    row = conn.execute(
        "SELECT * FROM paypal_orders WHERE paypal_order_id = ?", (order_id,)
    ).fetchone()
    if not row:
        conn.close()
        return jsonify(error="order not found"), 404
    if row["status"] == "captured":
        conn.close()
        return jsonify(ok=True, already=True)

    try:
        pp = paypal_api("POST", f"/v2/checkout/orders/{order_id}/capture", {})
    except Exception:
        conn.close()
        return jsonify(error="PayPal capture failed"), 502

    completed = any(
        c.get("status") == "COMPLETED"
        for pu in pp.get("purchase_units", [])
        for c in (pu.get("payments") or {}).get("captures", [])
    )
    if not completed:
        conn.close()
        return jsonify(error="payment not completed"), 402

    now = datetime.now(timezone.utc).isoformat()
    code = row["gift_card_code"] or ""
    discount = row["gift_card_discount_cents"] or 0
    if code and discount > 0:
        cur = conn.execute(
            "UPDATE gift_cards SET balance_cents = balance_cents - ?"
            " WHERE code = ? AND balance_cents >= ?",
            (discount, code, discount),
        )
        if cur.rowcount:
            conn.execute(
                "INSERT INTO redemptions (code, amount_cents, order_ref, created_at) VALUES (?, ?, ?, ?)",
                (code, discount, order_id, now),
            )

    promo = row["promo_code"] or ""
    payer = pp.get("payer") or {}
    email = row["email"] or payer.get("email_address") or ""
    name = (payer.get("name") or {}).get("given_name") or ""
    if promo and email:
        conn.execute(
            "INSERT OR IGNORE INTO promo_redemptions (code, email, stripe_session_id, created_at) VALUES (?, ?, ?, ?)",
            (promo, email, order_id, now),
        )

    try:
        if email:
            send_email(
                email,
                "Your Pop-A-Licious order is confirmed!",
                order_email_html(name, row["items_summary"], row["amount_total_cents"], code, discount, promo),
            )
    except Exception:
        pass  # payment already captured; never fail the response on email

    shipping = ""
    try:
        pu0 = (pp.get("purchase_units") or [{}])[0]
        sh = pu0.get("shipping") or {}
        sh_name = sh.get("name")
        sh_name = sh_name.get("full_name") if isinstance(sh_name, dict) else sh_name
        addr = sh.get("address") or {}
        shipping = ", ".join(
            x for x in [
                sh_name,
                addr.get("address_line_1"), addr.get("address_line_2"),
                addr.get("admin_area_2"), addr.get("admin_area_1"),
                addr.get("postal_code"), addr.get("country_code"),
            ] if x
        )
    except Exception:
        pass
    # Shippo label from the PayPal shipping address (never blocks the order).
    pu0 = (pp.get("purchase_units") or [{}])[0]
    psh = pu0.get("shipping") or {}
    psh_name = psh.get("name")
    psh_name = psh_name.get("full_name") if isinstance(psh_name, dict) else psh_name
    paddr = psh.get("address") or {}
    label_url, tracking_number = _create_shippo_label(
        _shippo_address_to(
            name=psh_name or name,
            street1=paddr.get("address_line_1", ""),
            street2=paddr.get("address_line_2", ""),
            city=paddr.get("admin_area_2", ""),
            state=paddr.get("admin_area_1", ""),
            zip_code=paddr.get("postal_code", ""),
            country=paddr.get("country_code", "US"),
        ),
        row["total_qty"] or 0,
        order_ref=f"paypal:{order_id}",
    )
    label_created_at = now if label_url else ""
    notify_merchant_of_order(order_id, name, email, row["items_summary"],
                             row["amount_total_cents"], code, discount,
                             promo, shipping, label_url or "", tracking_number or "")

    conn.execute("UPDATE paypal_orders SET status = 'captured' WHERE paypal_order_id = ?", (order_id,))
    prcode = row["reward_code"] or ""
    conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, total_qty,
            shippo_label_url, shippo_tracking_number, shippo_label_created_at,
            created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (f"paypal:{order_id}", email, name, shipping, row["items_summary"],
         row["amount_total_cents"], code, discount, promo, prcode,
         row["total_qty"] or 0, label_url or "", tracking_number or "",
         label_created_at, now),
    )
    # Loyalty: mark a redeemed reward code as used (single use).
    rcode = prcode
    if rcode:
        conn.execute(
            "UPDATE loyalty_rewards SET used = 1, used_at = ? WHERE code = ? AND used = 0",
            (now, rcode),
        )
    # Printful: forward any merch items to Printful for POD fulfillment.
    merch_items = _parse_merch_items(row["items_summary"])
    if merch_items:
        pf_recipient = {
            "name": psh_name or name,
            "address1": paddr.get("address_line_1", ""),
            "address2": paddr.get("address_line_2", ""),
            "city": paddr.get("admin_area_2", ""),
            "state_code": paddr.get("admin_area_1", ""),
            "country_code": paddr.get("country_code", "US"),
            "zip": paddr.get("postal_code", ""),
            "email": email,
        }
        pf_id, pf_err = submit_printful_order(pf_recipient, merch_items,
                                              order_ref=f"paypal:{order_id}")
        if pf_id:
            conn.execute(
                "UPDATE orders SET printful_order_id = ?, printful_status = 'submitted'"
                " WHERE stripe_session_id = ?",
                (str(pf_id), f"paypal:{order_id}"),
            )
    # Analytics: this shopper's cart converted — not abandoned.
    if email:
        conn.execute(
            "UPDATE cart_events SET ordered = 1 WHERE email = ? AND ordered = 0",
            (email,),
        )
    # Loyalty: credit Kernels (1 per $1 of total charged) to the member's account.
    if email:
        urow = conn.execute(
            "SELECT id FROM users WHERE email = ?", (email,)
        ).fetchone()
        if urow:
            _credit_kernels(conn, urow["id"],
                            (row["amount_total_cents"] or 0) // 100 * KERNELS_PER_DOLLAR,
                            "purchase", order_ref=f"paypal:{order_id}")
    conn.commit()
    conn.close()
    return jsonify(ok=True)


# ---------------------------------------------------------------- customer auth

def _auth_serializer():
    if not AUTH_SECRET:
        return None
    return URLSafeTimedSerializer(AUTH_SECRET, salt="popalicious-auth")

def _require_auth_ready():
    if not AUTH_SECRET:
        return jsonify(error="accounts are not set up yet"), 503
    return None

def _issue_auth_token(user_id):
    return _auth_serializer().dumps({"uid": user_id})

def _auth_user_from_token(token):
    s = _auth_serializer()
    if not s or not token:
        return None
    try:
        payload = s.loads(token, max_age=30 * 24 * 3600)  # 30 days
    except (BadSignature, SignatureExpired):
        return None
    conn = db()
    row = conn.execute(
        "SELECT id, email, name FROM users WHERE id = ? AND active = 1", (payload.get("uid"),)
    ).fetchone()
    conn.close()
    return row

# Sessions live in a secure HttpOnly cookie set by the backend (never in
# browser storage). SameSite=None + Secure lets the site on muse.ai use it
# cross-origin; every auth fetch must use credentials: "include".
SESSION_COOKIE = "pal_session"
SESSION_MAX_AGE = 30 * 24 * 3600

def _set_session_cookie(resp, token):
    resp.set_cookie(
        SESSION_COOKIE,
        token,
        max_age=SESSION_MAX_AGE,
        httponly=True,
        secure=True,
        samesite="None",
        path="/",
    )
    return resp

def _clear_session_cookie(resp):
    resp.delete_cookie(SESSION_COOKIE, path="/", samesite="None", secure=True)
    return resp

def _session_token_from_request():
    return request.cookies.get(SESSION_COOKIE, "")

def _send_verification_email(name, email, token):
    link = f"{SITE_URL}/#verify?token={token}"
    first = (name or "").split(" ")[0] or "there"
    html = (
        "<html><body style=\"font-family:Arial,sans-serif\">"
        f"<p>Hi {first},</p>"
        "<p>Thanks for creating a Pop-A-Licious account! "
        "Click the link below to verify your email address:</p>"
        f"<p><a href=\"{link}\">Verify my account</a></p>"
        "<p>This link expires in 24 hours.</p>"
        "<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>"
        "</body></html>"
    )
    send_email(email, "Verify your Pop-A-Licious account", html)

@app.post("/api/auth/signup")
def auth_signup():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""
    if not name:
        return jsonify(error="please enter your name"), 400
    if not EMAIL_RE.match(email):
        return jsonify(error="please enter a valid email address"), 400
    if len(password) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    conn = db()
    existing = conn.execute(
        "SELECT id, active FROM users WHERE email = ?", (email,)
    ).fetchone()
    if existing:
        if existing["active"]:
            conn.close()
            return jsonify(error="an account with this email already exists — try logging in"), 409
        # Deactivated account: remove it and its old tokens so the email
        # re-registers completely fresh, like a new address.
        conn.execute("DELETE FROM verification_tokens WHERE user_id = ?", (existing["id"],))
        conn.execute("DELETE FROM password_reset_tokens WHERE user_id = ?", (existing["id"],))
        conn.execute("DELETE FROM users WHERE id = ?", (existing["id"],))
        conn.commit()
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO users (email, name, password_hash, verified, created_at)"
        " VALUES (?, ?, ?, 0, ?)",
        (email, name, generate_password_hash(password), now),
    )
    user_id = cur.lastrowid
    token = secrets.token_urlsafe(32)
    expires = (datetime.now(timezone.utc) + timedelta(hours=24)).isoformat()
    conn.execute(
        "INSERT INTO verification_tokens (token, user_id, expires_at) VALUES (?, ?, ?)",
        (token, user_id, expires),
    )
    # Staff referral: if the signup came from an employee's QR code, credit them.
    staff_ref = (data.get("staff_ref") or "").strip().upper()
    if staff_ref:
        srow = conn.execute(
            "SELECT id FROM staff WHERE referral_code = ? AND active = 1",
            (staff_ref,),
        ).fetchone()
        if srow:
            _credit_staff_kernels(conn, srow["id"], 1, "member_signup", ref=email)
    conn.commit()
    conn.close()
    email_error = None
    try:
        _send_verification_email(name, email, token)
    except Exception as e:
        email_error = str(e)
    resp = jsonify(ok=True)
    if email_error:
        resp = jsonify(ok=True, email_error=email_error)
    return resp

@app.get("/api/auth/verify")
def auth_verify():
    err = _require_auth_ready()
    if err:
        return err
    token = request.args.get("token", "")
    conn = db()
    row = conn.execute(
        "SELECT user_id, expires_at, used FROM verification_tokens WHERE token = ?",
        (token,),
    ).fetchone()
    if not row or row["used"]:
        # Idempotent: if the token's account is already verified, count it as
        # success (covers double-clicks and email clients that pre-fetch links).
        if row:
            urow = conn.execute(
                "SELECT verified FROM users WHERE id = ?", (row["user_id"],)
            ).fetchone()
            if urow and urow["verified"]:
                conn.close()
                return jsonify(ok=True)
        conn.close()
        return jsonify(error="this verification link is invalid or already used"), 400
    if datetime.fromisoformat(row["expires_at"]) < datetime.now(timezone.utc):
        conn.close()
        return jsonify(error="this verification link has expired — request a new one"), 400
    conn.execute("UPDATE users SET verified = 1 WHERE id = ?", (row["user_id"],))
    conn.execute("UPDATE verification_tokens SET used = 1 WHERE token = ?", (token,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/auth/resend-verification")
def auth_resend():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    email_error = None
    conn = db()
    row = conn.execute(
        "SELECT id, name, verified FROM users WHERE email = ?", (email,)
    ).fetchone()
    if row and not row["verified"]:
        token = secrets.token_urlsafe(32)
        expires = (datetime.now(timezone.utc) + timedelta(hours=24)).isoformat()
        conn.execute(
            "INSERT INTO verification_tokens (token, user_id, expires_at) VALUES (?, ?, ?)",
            (token, row["id"], expires),
        )
        conn.commit()
        try:
            _send_verification_email(row["name"], email, token)
        except Exception as e:
            email_error = str(e)
    conn.close()
    if email_error:
        return jsonify(ok=True, email_error=email_error)
    return jsonify(ok=True)

def _send_password_reset_email(name, email, token):
    link = f"{SITE_URL}/#reset-password?token={token}"
    first = (name or "").split(" ")[0] or "there"
    html = (
        "<html><body style=\"font-family:Arial,sans-serif\">"
        f"<p>Hi {first},</p>"
        "<p>Someone requested a password reset for your Pop-A-Licious account. "
        "Click the link below to choose a new password:</p>"
        f"<p><a href=\"{link}\">Reset my password</a></p>"
        "<p>This link expires in 1 hour. If you didn't request this, just ignore this email.</p>"
        "<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>"
        "</body></html>"
    )
    send_email(email, "Reset your Pop-A-Licious password", html)

@app.post("/api/auth/forgot-password")
def auth_forgot_password():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    conn = db()
    row = conn.execute(
        "SELECT id, name, active FROM users WHERE email = ?", (email,)
    ).fetchone()
    if row and row["active"]:
        token = secrets.token_urlsafe(32)
        expires = (datetime.now(timezone.utc) + timedelta(hours=1)).isoformat()
        conn.execute(
            "INSERT INTO password_reset_tokens (token, user_id, expires_at) VALUES (?, ?, ?)",
            (token, row["id"], expires),
        )
        conn.commit()
        try:
            _send_password_reset_email(row["name"], email, token)
        except Exception:
            pass  # never reveal whether the email exists or sending failed
    conn.close()
    return jsonify(ok=True)

@app.post("/api/auth/reset-password")
def auth_reset_password():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    token = data.get("token") or ""
    password = data.get("password") or ""
    if len(password) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    conn = db()
    row = conn.execute(
        "SELECT user_id, expires_at, used FROM password_reset_tokens WHERE token = ?",
        (token,),
    ).fetchone()
    if not row or row["used"]:
        conn.close()
        return jsonify(error="this reset link is invalid or already used"), 400
    if datetime.fromisoformat(row["expires_at"]) < datetime.now(timezone.utc):
        conn.close()
        return jsonify(error="this reset link has expired — request a new one"), 400
    conn.execute(
        "UPDATE users SET password_hash = ? WHERE id = ?",
        (generate_password_hash(password), row["user_id"]),
    )
    conn.execute("UPDATE password_reset_tokens SET used = 1 WHERE token = ?", (token,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/auth/login")
def auth_login():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""
    conn = db()
    row = conn.execute(
        "SELECT id, name, email, password_hash, verified, active, created_at,"
        " anniversary_credited_year, last_notified_balance FROM users WHERE email = ?",
        (email,),
    ).fetchone()
    if not row or not row["password_hash"] or not check_password_hash(
        row["password_hash"], password
    ):
        conn.close()
        return jsonify(error="email or password is incorrect"), 401
    if not row["active"]:
        conn.close()
        return jsonify(error="this account has been deactivated"), 403
    if not row["verified"]:
        conn.close()
        return jsonify(
            error="please verify your email before logging in — check your inbox",
            needs_verification=True,
        ), 403
    # Anniversary kernels: 10 Kernels every year on the member's join date.
    anniversary_credited = False
    try:
        joined = datetime.fromisoformat(row["created_at"])
        now = datetime.now(timezone.utc)
        if (joined.month, joined.day) == (now.month, now.day):
            if (row["anniversary_credited_year"] or 0) < now.year:
                _credit_kernels(conn, row["id"], 10, "anniversary",
                                order_ref=f"{now.year} anniversary")
                conn.execute(
                    "UPDATE users SET anniversary_credited_year = ? WHERE id = ?",
                    (now.year, row["id"]),
                )
                anniversary_credited = True
    except Exception:
        pass
    # Kernel notification: how many earned since last login.
    # First tracked login seeds the baseline silently (no retroactive blast).
    balance = _kernel_balance(conn, row["id"])
    last_notified = row["last_notified_balance"] or 0
    if last_notified == 0 and balance > 0:
        # Existing users pre-feature: seed silently, notify on future earnings.
        kernels_earned = 0
    else:
        kernels_earned = max(balance - last_notified, 0)
    conn.execute(
        "UPDATE users SET last_notified_balance = ? WHERE id = ?",
        (balance, row["id"]),
    )
    conn.commit()
    conn.close()
    token = _issue_auth_token(row["id"])
    resp = jsonify(name=row["name"], email=row["email"], token=token,
                   kernels_earned=kernels_earned,
                   anniversary_credited=anniversary_credited)
    return _set_session_cookie(resp, token)

@app.get("/api/admin/is-admin")
def admin_is_admin():
    """Public check: is this email an admin? Used for auto-redirect on login."""
    email = (request.args.get("email") or "").strip().lower()
    return jsonify(is_admin=email in ADMIN_EMAILS)

@app.post("/api/admin/login")
def admin_login():
    """Password-based admin login. Email must be in ADMIN_EMAILS."""
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""
    if email not in ADMIN_EMAILS:
        return jsonify(error="not an admin email"), 403
    conn = db()
    row = conn.execute(
        "SELECT id, name, email, password_hash, verified, active FROM users WHERE email = ?",
        (email,),
    ).fetchone()
    conn.close()
    if not row or not row["password_hash"] or not check_password_hash(
        row["password_hash"], password
    ):
        return jsonify(error="email or password is incorrect"), 401
    if not row["active"]:
        return jsonify(error="this account has been deactivated"), 403
    token = _issue_auth_token(row["id"])
    resp = jsonify(name=row["name"], email=row["email"], token=token, is_admin=True)
    return _set_session_cookie(resp, token)

@app.post("/api/auth/logout")
def auth_logout():
    err = _require_auth_ready()
    if err:
        return err
    return _clear_session_cookie(jsonify(ok=True))

@app.get("/api/auth/me")
def auth_me():
    err = _require_auth_ready()
    if err:
        return err
    auth = request.headers.get("Authorization", "")
    token = auth[7:] if auth.startswith("Bearer ") else ""
    row = _auth_user_from_token(token or _session_token_from_request())
    if not row:
        return jsonify(error="not logged in"), 401
    return jsonify(id=row["id"], name=row["name"], email=row["email"],
                   is_admin=row["email"].lower() in ADMIN_EMAILS)

@app.get("/api/auth/google/start")
def google_start():
    err = _require_auth_ready()
    if err:
        return err
    if not GOOGLE_CLIENT_ID:
        return jsonify(error="Google sign-in is not set up yet"), 400
    state = _auth_serializer().dumps({"nonce": secrets.token_urlsafe(8)})
    params = {
        "client_id": GOOGLE_CLIENT_ID,
        "redirect_uri": BACKEND_URL + "/api/auth/google/callback",
        "response_type": "code",
        "scope": "openid email profile",
        "state": state,
        "prompt": "select_account",
    }
    return redirect(
        "https://accounts.google.com/o/oauth2/v2/auth?" + urlencode(params)
    )

@app.get("/api/auth/google/callback")
def google_callback():
    err = _require_auth_ready()
    if err:
        return err
    if not (GOOGLE_CLIENT_ID and GOOGLE_CLIENT_SECRET):
        return jsonify(error="Google sign-in is not set up yet"), 400
    code = request.args.get("code", "")
    state = request.args.get("state", "")
    try:
        _auth_serializer().loads(state, max_age=600)
    except (BadSignature, SignatureExpired):
        return jsonify(error="invalid sign-in request"), 400
    try:
        tok = requests.post(
            "https://oauth2.googleapis.com/token",
            data={
                "client_id": GOOGLE_CLIENT_ID,
                "client_secret": GOOGLE_CLIENT_SECRET,
                "code": code,
                "grant_type": "authorization_code",
                "redirect_uri": BACKEND_URL + "/api/auth/google/callback",
            },
            timeout=20,
        )
        tok.raise_for_status()
        access_token = tok.json()["access_token"]
        me = requests.get(
            "https://www.googleapis.com/oauth2/v3/userinfo",
            headers={"Authorization": f"Bearer {access_token}"},
            timeout=20,
        )
        me.raise_for_status()
        info = me.json()
    except Exception:
        return jsonify(error="Google sign-in failed"), 502
    google_id = info.get("sub", "")
    email = (info.get("email") or "").strip().lower()
    name = (info.get("name") or "").strip()
    if not google_id or not email:
        return jsonify(error="Google sign-in failed"), 502
    conn = db()
    row = conn.execute(
        "SELECT id FROM users WHERE google_id = ? OR email = ?", (google_id, email)
    ).fetchone()
    now = datetime.now(timezone.utc).isoformat()
    if row:
        user_id = row["id"]
        conn.execute(
            "UPDATE users SET google_id = ?, verified = 1 WHERE id = ?",
            (google_id, user_id),
        )
    else:
        cur = conn.execute(
            "INSERT INTO users (email, name, password_hash, verified, google_id, created_at)"
            " VALUES (?, ?, '', 1, ?, ?)",
            (email, name, google_id, now),
        )
        user_id = cur.lastrowid
    conn.commit()
    conn.close()
    token = _issue_auth_token(user_id)
    return _set_session_cookie(redirect(f"{SITE_URL}/#login"), token)


# Reviews are held for approval: only approved=1 reviews are public.
# Admins (emails in ADMIN_EMAILS) approve via the hidden /admin-reviews page.
ADMIN_EMAILS = [
    e.strip().lower()
    for e in os.environ.get("ADMIN_EMAILS", "").split(",")
    if e.strip()
]

def _is_admin(user):
    return bool(user) and (user["email"].lower() in ADMIN_EMAILS)

# ---------------- Pop-A-Licious Rewards (loyalty program) ----------------
# Members earn Kernels (1 per $1 by default, never expire). Tiers:
#   25 Kernels → free shipping | 50 → free bag | 150 → free 3-pack | 300 → free 6-pack
# Status: Popped → Buttery → Golden Kernel (by lifetime Kernels earned).

KERNELS_PER_DOLLAR = int(os.environ.get("KERNELS_PER_DOLLAR", "1"))
LOYALTY_TIER_BUTTERY_AT = int(os.environ.get("LOYALTY_TIER_BUTTERY_AT", "300"))
LOYALTY_TIER_GOLDEN_AT = int(os.environ.get("LOYALTY_TIER_GOLDEN_AT", "1000"))

REWARD_TIERS = {
    "free_bag": {"kernels": 50, "label": "Free single bag"},
    "free_shipping": {"kernels": 100, "label": "Free shipping on one order"},
    "free_3pack": {"kernels": 150, "label": "Free 3-pack"},
    "free_6pack": {"kernels": 300, "label": "Free 6-pack"},
}
# Employee reward tiers — simpler scale matching the 1-kernel-per-signup earn rate.
STAFF_REWARD_TIERS = {
    "free_bag": {"kernels": 10, "label": "Free single bag", "kind": "popcorn"},
    "free_3pack": {"kernels": 25, "label": "Free 3-pack", "kind": "popcorn"},
    "free_6pack": {"kernels": 50, "label": "Free 6-pack", "kind": "popcorn"},
    "giftcard_10": {"kernels": 75, "label": "$10 gift card of your choice",
                    "kind": "giftcard_choice", "amount_cents": 1000},
    "giftcard_25": {"kernels": 150, "label": "$25 gift card of your choice",
                    "kind": "giftcard_choice", "amount_cents": 2500},
}
# Discount applied at checkout per reward type ("shipping" = free shipping).
REWARD_DISCOUNT_CENTS = {
    "free_shipping": "shipping",
    "free_bag": 800,
    "free_3pack": 2100,
    "free_6pack": 4000,
    "birthday_bag": 800,
}

def _kernel_balance(conn, user_id):
    row = conn.execute(
        "SELECT COALESCE(SUM(kernels), 0) AS bal FROM kernel_transactions WHERE user_id = ?",
        (user_id,),
    ).fetchone()
    return int(row["bal"])

def _lifetime_kernels(conn, user_id):
    row = conn.execute(
        "SELECT COALESCE(SUM(kernels), 0) AS tot FROM kernel_transactions"
        " WHERE user_id = ? AND kernels > 0",
        (user_id,),
    ).fetchone()
    return int(row["tot"])

def _loyalty_tier(lifetime):
    if lifetime >= LOYALTY_TIER_GOLDEN_AT:
        return "Golden Kernel"
    if lifetime >= LOYALTY_TIER_BUTTERY_AT:
        return "Buttery"
    return "Popped"

def _credit_kernels(conn, user_id, kernels, reason, order_ref="", staff_id=None):
    if kernels <= 0:
        return 0
    conn.execute(
        "INSERT INTO kernel_transactions (user_id, kernels, reason, order_ref, staff_id, created_at)"
        " VALUES (?, ?, ?, ?, ?, ?)",
        (user_id, kernels, reason, order_ref, staff_id,
         datetime.now(timezone.utc).isoformat()),
    )
    return kernels

def _debit_kernels(conn, user_id, kernels, reason, order_ref="", staff_id=None):
    if kernels <= 0:
        return False
    if _kernel_balance(conn, user_id) < kernels:
        return False
    conn.execute(
        "INSERT INTO kernel_transactions (user_id, kernels, reason, order_ref, staff_id, created_at)"
        " VALUES (?, ?, ?, ?, ?, ?)",
        (user_id, -kernels, reason, order_ref, staff_id,
         datetime.now(timezone.utc).isoformat()),
    )
    return True

def _new_reward_code():
    return "KERN-" + secrets.token_hex(4).upper()

def _maybe_grant_birthday_reward(conn, user_id):
    """Grant the yearly free birthday bag if it's the member's birthday month."""
    row = conn.execute(
        "SELECT birthday FROM users WHERE id = ?", (user_id,)
    ).fetchone()
    bday = (row["birthday"] or "") if row else ""
    if not bday:
        return None
    try:
        month = int(bday.split("-")[1])
    except (IndexError, ValueError):
        return None
    if month != datetime.now(timezone.utc).month:
        return None
    year = str(datetime.now().year)
    exists = conn.execute(
        "SELECT 1 FROM loyalty_rewards WHERE user_id = ? AND reward_type = 'birthday_bag'"
        " AND substr(created_at, 1, 4) = ?",
        (user_id, year),
    ).fetchone()
    if exists:
        return None
    code = _new_reward_code()
    conn.execute(
        "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent, created_at)"
        " VALUES (?, 'birthday_bag', ?, 0, ?)",
        (user_id, code, datetime.now(timezone.utc).isoformat()),
    )
    return code

def _current_member():
    """The logged-in customer (or None). Accepts the Bearer token or session cookie."""
    err = _require_auth_ready()
    if err:
        return None
    auth = request.headers.get("Authorization", "")
    token = auth[7:] if auth.startswith("Bearer ") else ""
    row = _auth_user_from_token(token or _session_token_from_request())
    return row

# ---------------- staff sessions (individual logins, loyalty tools only) ----------------
STAFF_COOKIE = "pal_staff"

def _staff_serializer():
    if not AUTH_SECRET:
        return None
    return URLSafeTimedSerializer(AUTH_SECRET, salt="popalicious-staff")

def _issue_staff_token(staff_id):
    return _staff_serializer().dumps({"sid": staff_id})

def _staff_from_request():
    s = _staff_serializer()
    token = request.cookies.get(STAFF_COOKIE, "")
    if not token:
        # Fall back to the Authorization header (mobile/Safari cookie blockers).
        auth = request.headers.get("Authorization", "")
        if auth.lower().startswith("bearer "):
            token = auth[7:].strip()
    if not s or not token:
        return None
    try:
        payload = s.loads(token, max_age=12 * 3600)  # 12-hour staff sessions
    except (BadSignature, SignatureExpired):
        return None
    conn = db()
    row = conn.execute(
        "SELECT id, email, name FROM staff WHERE id = ? AND active = 1 AND verified = 1",
        (payload.get("sid"),),
    ).fetchone()
    conn.close()
    return row

def _require_staff():
    staff = _staff_from_request()
    if not staff:
        return None, (jsonify(error="staff login required"), 401)
    return staff, None


# ---------------- wholesale customer auth (ERP Phase 5) ----------------

def _wholesale_serializer():
    if not AUTH_SECRET:
        return None
    return URLSafeTimedSerializer(AUTH_SECRET, salt="popalicious-wholesale")


def _issue_wholesale_token(user_id):
    return _wholesale_serializer().dumps({"wid": user_id})


def _wholesale_user_from_request():
    """Wholesale customer from Bearer token. Returns (user_row, account_row)
    or (None, None). Requires user active AND account active + not deactivated."""
    s = _wholesale_serializer()
    auth = request.headers.get("Authorization", "")
    if not auth.lower().startswith("bearer "):
        return None, None
    token = auth[7:].strip()
    if not s or not token:
        return None, None
    try:
        payload = s.loads(token, max_age=30 * 24 * 3600)  # 30-day sessions
    except (BadSignature, SignatureExpired):
        return None, None
    conn = db()
    user = conn.execute(
        "SELECT wu.*, wa.name AS account_name, wa.account_status,"
        " wa.active AS account_active, wa.savory_price_cents,"
        " wa.sweet_price_cents, wa.default_po, wa.price_per_bag_cents"
        " FROM erp_wholesale_users wu"
        " JOIN erp_wholesale_accounts wa ON wa.id = wu.account_id"
        " WHERE wu.id = ? AND wu.active = 1",
        (payload.get("wid"),)).fetchone()
    conn.close()
    if not user:
        return None, None
    if not user["account_active"] or user["account_status"] == "deactivated":
        return None, None
    return user, user


def _require_wholesale():
    """Wholesale customer only. Returns ((user, account), None) or
    (None, (resp, code)). 401 when no/invalid token, 403 for other logins."""
    user, _acct = _wholesale_user_from_request()
    if user:
        return (user, user), None
    auth = request.headers.get("Authorization", "")
    if auth.lower().startswith("bearer "):
        return None, (jsonify(error="wholesale customer login required"), 403)
    return None, (jsonify(error="wholesale customer login required"), 401)

def _set_staff_cookie(resp, token):
    resp.set_cookie(
        STAFF_COOKIE, token, max_age=12 * 3600, httponly=True,
        secure=True, samesite="None", path="/",
    )
    return resp

def _clear_staff_cookie(resp):
    resp.delete_cookie(STAFF_COOKIE, path="/", samesite="None", secure=True)
    return resp

# ---------------- member loyalty endpoints ----------------

@app.get("/api/loyalty/status")
def loyalty_status():
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    conn = db()
    _maybe_grant_birthday_reward(conn, user["id"])
    conn.commit()
    balance = _kernel_balance(conn, user["id"])
    lifetime = _lifetime_kernels(conn, user["id"])
    brow = conn.execute(
        "SELECT birthday, created_at FROM users WHERE id = ?", (user["id"],)
    ).fetchone()
    rewards = conn.execute(
        "SELECT reward_type, code, created_at FROM loyalty_rewards"
        " WHERE user_id = ? AND used = 0 ORDER BY created_at DESC",
        (user["id"],),
    ).fetchall()
    conn.close()
    return jsonify(
        kernels=balance,
        lifetime_kernels=lifetime,
        tier=_loyalty_tier(lifetime),
        birthday=(brow["birthday"] or "") if brow else "",
        member_since=(brow["created_at"] or "") if brow else "",
        kernels_per_dollar=KERNELS_PER_DOLLAR,
        reward_tiers={k: v["kernels"] for k, v in REWARD_TIERS.items()},
        available_rewards=[
            {"type": r["reward_type"], "code": r["code"],
             "label": REWARD_TIERS.get(r["reward_type"], {}).get("label", "Birthday reward"),
             "created_at": r["created_at"]}
            for r in rewards
        ],
    )

@app.get("/api/loyalty/history")
def loyalty_history():
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    conn = db()
    rows = conn.execute(
        "SELECT kt.kernels, kt.reason, kt.order_ref, kt.created_at, s.name AS staff_name"
        " FROM kernel_transactions kt LEFT JOIN staff s ON s.id = kt.staff_id"
        " WHERE kt.user_id = ? ORDER BY kt.id DESC LIMIT 50",
        (user["id"],),
    ).fetchall()
    conn.close()
    return jsonify(history=[
        {"kernels": r["kernels"], "reason": r["reason"],
         "order_ref": r["order_ref"], "created_at": r["created_at"],
         "staff_name": r["staff_name"] or ""}
        for r in rows
    ])

@app.post("/api/loyalty/redeem")
def loyalty_redeem():
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    data = request.get_json(force=True) or {}
    reward_type = (data.get("reward_type") or "").strip()
    tier = REWARD_TIERS.get(reward_type)
    if not tier:
        return jsonify(error="unknown reward"), 400
    conn = db()
    code = _new_reward_code()
    if not _debit_kernels(conn, user["id"], tier["kernels"], "redemption",
                          order_ref=code):
        conn.close()
        return jsonify(error="not enough Kernels"), 402
    conn.execute(
        "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent, created_at)"
        " VALUES (?, ?, ?, ?, ?)",
        (user["id"], reward_type, code, tier["kernels"],
         datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True, code=code, label=tier["label"])

@app.post("/api/loyalty/birthday")
def loyalty_birthday():
    """Save the member's birthday (enables the birthday reward)."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    data = request.get_json(force=True) or {}
    bday = (data.get("birthday") or "").strip()
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", bday):
        return jsonify(error="birthday must be YYYY-MM-DD"), 400
    conn = db()
    conn.execute("UPDATE users SET birthday = ? WHERE id = ?", (bday, user["id"]))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

# ---------------- staff loyalty endpoints ----------------

def _send_staff_password_reset_email(name, email, token):
    link = f"{SITE_URL}/#staff-reset-password?token={token}"
    first = (name or "").split(" ")[0] or "there"
    html = (
        "<html><body style=\"font-family:Arial,sans-serif\">"
        f"<p>Hi {first},</p>"
        "<p>Someone requested a password reset for your Pop-A-Licious staff account. "
        "Click the link below to choose a new password:</p>"
        f"<p><a href=\"{link}\">Reset my staff password</a></p>"
        "<p>This link expires in 1 hour. If you didn't request this, just ignore this email.</p>"
        "<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>"
        "</body></html>"
    )
    send_email(email, "Reset your Pop-A-Licious staff password", html)

@app.post("/api/loyalty/staff/forgot-password")
def staff_forgot_password():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    conn = db()
    row = conn.execute(
        "SELECT id, name, active FROM staff WHERE email = ?", (email,)
    ).fetchone()
    if row and row["active"]:
        token = secrets.token_urlsafe(32)
        expires = (datetime.now(timezone.utc) + timedelta(hours=1)).isoformat()
        conn.execute(
            "INSERT INTO staff_password_reset_tokens (token, staff_id, expires_at) VALUES (?, ?, ?)",
            (token, row["id"], expires),
        )
        conn.commit()
        try:
            _send_staff_password_reset_email(row["name"], email, token)
        except Exception:
            pass  # never reveal whether the email exists or sending failed
    conn.close()
    return jsonify(ok=True)

@app.post("/api/loyalty/staff/reset-password")
def staff_reset_password():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    token = data.get("token") or ""
    password = data.get("password") or ""
    if len(password) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    conn = db()
    row = conn.execute(
        "SELECT staff_id, expires_at, used FROM staff_password_reset_tokens WHERE token = ?",
        (token,),
    ).fetchone()
    if not row or row["used"]:
        conn.close()
        return jsonify(error="this reset link is invalid or already used"), 400
    if datetime.fromisoformat(row["expires_at"]) < datetime.now(timezone.utc):
        conn.close()
        return jsonify(error="this reset link has expired — request a new one"), 400
    conn.execute(
        "UPDATE staff SET password_hash = ? WHERE id = ?",
        (generate_password_hash(password), row["staff_id"]),
    )
    conn.execute("UPDATE staff_password_reset_tokens SET used = 1 WHERE token = ?", (token,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/loyalty/staff/login")
def staff_login():
    err = _require_auth_ready()
    if err:
        return err
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""
    conn = db()
    row = conn.execute(
        "SELECT id, email, name, password_hash, verified FROM staff WHERE email = ? AND active = 1",
        (email,),
    ).fetchone()
    if not row or not check_password_hash(row["password_hash"], password):
        conn.close()
        return jsonify(error="invalid staff login"), 401
    if not row["verified"]:
        conn.close()
        return jsonify(error="please verify your account via the email we sent"), 403
    # Auto-credit birthday + work-anniversary kernels (once per year each).
    occasion_credits = _maybe_credit_staff_occasions(conn, row["id"])
    conn.commit()
    conn.close()
    staff_token = _issue_staff_token(row["id"])
    return _set_staff_cookie(
        jsonify(ok=True, name=row["name"], email=row["email"],
                occasion_credits=occasion_credits, token=staff_token),
        staff_token,
    )

@app.post("/api/loyalty/staff/logout")
def staff_logout():
    return _clear_staff_cookie(jsonify(ok=True))

@app.get("/api/orders/mine")
def my_orders():
    """Order history for the logged-in customer."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    conn = db()
    rows = conn.execute(
        "SELECT stripe_session_id, items_summary, amount_total_cents, created_at"
        " FROM orders WHERE email = ? ORDER BY id DESC LIMIT 25",
        (user["email"],),
    ).fetchall()
    conn.close()
    return jsonify(orders=[
        {"id": r["stripe_session_id"], "items": r["items_summary"] or "",
         "total_cents": r["amount_total_cents"] or 0, "created_at": r["created_at"]}
        for r in rows
    ])

@app.get("/api/loyalty/staff/me")
def staff_me():
    staff, err = _require_staff()
    if err:
        return err[0], err[1]
    return jsonify(id=staff["id"], email=staff["email"], name=staff["name"])

@app.get("/api/loyalty/staff/members")
def staff_member_search():
    staff, err = _require_staff()
    if err:
        return err[0], err[1]
    q = (request.args.get("q") or "").strip()
    if not q:
        return jsonify(members=[])
    # Accept a scanned member QR code (full URL with ?member=PAL:<id>),
    # a raw PAL:<user_id>, or email/name.
    conn = db()
    qr_member = ""
    if "member=" in q:
        # Extract member=... from a scanned QR URL.
        try:
            qr_member = q.split("member=", 1)[1].split("&")[0].split("#")[0].strip()
        except IndexError:
            qr_member = ""
    pal = qr_member or q
    if pal.upper().startswith("PAL:"):
        try:
            uid = int(pal.split(":", 1)[1])
        except ValueError:
            uid = -1
        rows = conn.execute(
            "SELECT id, email, name FROM users WHERE id = ?", (uid,)
        ).fetchall()
    else:
        like = f"%{q}%"
        rows = conn.execute(
            "SELECT id, email, name FROM users WHERE email LIKE ? OR name LIKE ? LIMIT 20",
            (like, like),
        ).fetchall()
    members = []
    for r in rows:
        members.append({
            "id": r["id"], "email": r["email"], "name": r["name"],
            "kernels": _kernel_balance(conn, r["id"]),
            "tier": _loyalty_tier(_lifetime_kernels(conn, r["id"])),
        })
    conn.close()
    return jsonify(members=members)

@app.post("/api/loyalty/staff/credit")
def staff_credit_kernels():
    """Credit Kernels for an in-person sale. Body: {user_id, amount_cents, note?}"""
    staff, err = _require_staff()
    if err:
        return err[0], err[1]
    data = request.get_json(force=True) or {}
    try:
        user_id = int(data.get("user_id") or 0)
        amount_cents = int(data.get("amount_cents") or 0)
    except (TypeError, ValueError):
        return jsonify(error="invalid input"), 400
    if user_id <= 0 or amount_cents <= 0 or amount_cents > 100000:
        return jsonify(error="invalid input"), 400
    kernels = max(amount_cents // 100 * KERNELS_PER_DOLLAR, 0)
    conn = db()
    mrow = conn.execute("SELECT active FROM users WHERE id = ?", (user_id,)).fetchone()
    if not mrow:
        conn.close()
        return jsonify(error="member not found"), 404
    if not mrow["active"]:
        conn.close()
        return jsonify(error="member account is deactivated"), 403
    _credit_kernels(conn, user_id, kernels, "in_person",
                    order_ref=(data.get("note") or "")[:120], staff_id=staff["id"])
    conn.commit()
    balance = _kernel_balance(conn, user_id)
    conn.close()
    return jsonify(ok=True, kernels_credited=kernels, balance=balance)

@app.post("/api/loyalty/staff/redeem")
def staff_redeem_for_member():
    """Redeem a reward on a member's behalf in person. Body: {user_id, reward_type}"""
    staff, err = _require_staff()
    if err:
        return err[0], err[1]
    data = request.get_json(force=True) or {}
    try:
        user_id = int(data.get("user_id") or 0)
    except (TypeError, ValueError):
        return jsonify(error="invalid input"), 400
    reward_type = (data.get("reward_type") or "").strip()
    tier = REWARD_TIERS.get(reward_type)
    if user_id <= 0 or not tier:
        return jsonify(error="invalid input"), 400
    conn = db()
    mrow = conn.execute("SELECT active FROM users WHERE id = ?", (user_id,)).fetchone()
    if not mrow:
        conn.close()
        return jsonify(error="member not found"), 404
    if not mrow["active"]:
        conn.close()
        return jsonify(error="member account is deactivated"), 403
    code = _new_reward_code()
    if not _debit_kernels(conn, user_id, tier["kernels"], "redemption_in_person",
                          order_ref=code, staff_id=staff["id"]):
        conn.close()
        return jsonify(error="not enough Kernels"), 402
    conn.execute(
        "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent, staff_id, created_at)"
        " VALUES (?, ?, ?, ?, ?, ?)",
        (user_id, reward_type, code, tier["kernels"], staff["id"],
         datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    balance = _kernel_balance(conn, user_id)
    conn.close()
    # In person the reward is applied on the spot, so mark it used immediately.
    conn = db()
    conn.execute(
        "UPDATE loyalty_rewards SET used = 1, used_at = ? WHERE code = ?",
        (datetime.now(timezone.utc).isoformat(), code),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True, label=tier["label"], balance=balance)

def _credit_staff_kernels(conn, staff_id, kernels, reason, ref=""):
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        "INSERT INTO staff_kernel_transactions (staff_id, kernels, reason, ref, created_at)"
        " VALUES (?, ?, ?, ?, ?)",
        (staff_id, kernels, reason, ref, now),
    )
    conn.execute(
        "UPDATE staff SET kernels = kernels + ? WHERE id = ?", (kernels, staff_id)
    )

def _maybe_credit_staff_occasions(conn, staff_id):
    """Auto-credit birthday (10) and work-anniversary (10) kernels on staff login."""
    row = conn.execute(
        "SELECT birthday, hire_date FROM staff WHERE id = ?", (staff_id,)
    ).fetchone()
    if not row:
        return []
    today = datetime.now(timezone.utc).date()
    year = str(today.year)
    credited = []
    # Birthday: 10 kernels once per year, during the birthday month.
    m = re.match(r"^\d{4}-(\d{2})-\d{2}$", (row["birthday"] or "").strip())
    if m and m.group(1) == f"{today.month:02d}":
        exists = conn.execute(
            "SELECT 1 FROM staff_kernel_transactions"
            " WHERE staff_id = ? AND reason = 'birthday' AND ref = ?",
            (staff_id, year),
        ).fetchone()
        if not exists:
            _credit_staff_kernels(conn, staff_id, 10, "birthday", ref=year)
            credited.append("birthday")
    # Work anniversary: 10 kernels once per year, on/after the anniversary date.
    hm = re.match(r"^(\d{4})-(\d{2})-(\d{2})$", (row["hire_date"] or "").strip())
    if hm:
        hire = datetime(int(hm.group(1)), int(hm.group(2)), int(hm.group(3))).date()
        years = today.year - hire.year - (
            (today.month, today.day) < (hire.month, hire.day))
        if years >= 1 and (today.month, today.day) >= (hire.month, hire.day):
            ref = f"{year}-{years}yr"
            exists = conn.execute(
                "SELECT 1 FROM staff_kernel_transactions"
                " WHERE staff_id = ? AND reason = 'anniversary' AND ref = ?",
                (staff_id, ref),
            ).fetchone()
            if not exists:
                _credit_staff_kernels(conn, staff_id, 10, "anniversary", ref=ref)
                credited.append(f"{years}-year anniversary")
    return credited

@app.get("/api/loyalty/staff/is-staff")
def staff_is_staff():
    """Public check: does this email belong to an active staff account?"""
    email = (request.args.get("email") or "").strip().lower()
    if not email:
        return jsonify(is_staff=False)
    conn = db()
    row = conn.execute(
        "SELECT 1 FROM staff WHERE email = ? AND active = 1", (email,)
    ).fetchone()
    conn.close()
    return jsonify(is_staff=bool(row))

@app.get("/api/loyalty/staff/verify-check")
def staff_verify_check():
    token = (request.args.get("token") or "").strip()
    conn = db()
    row = conn.execute(
        "SELECT t.staff_id, t.expires_at, s.name, s.email FROM staff_verification_tokens t"
        " JOIN staff s ON s.id = t.staff_id WHERE t.token = ?",
        (token,),
    ).fetchone()
    conn.close()
    if not row:
        return jsonify(error="invalid or expired link"), 400
    if row["expires_at"] < datetime.now(timezone.utc).isoformat():
        return jsonify(error="this link has expired"), 400
    return jsonify(ok=True, name=row["name"], email=row["email"])

@app.post("/api/loyalty/staff/set-password")
def staff_set_password():
    data = request.get_json(force=True) or {}
    token = (data.get("token") or "").strip()
    new = data.get("new_password") or ""
    confirm = data.get("confirm_password") or ""
    if len(new) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    if new != confirm:
        return jsonify(error="passwords do not match"), 400
    conn = db()
    row = conn.execute(
        "SELECT staff_id, expires_at FROM staff_verification_tokens WHERE token = ?",
        (token,),
    ).fetchone()
    if not row or row["expires_at"] < datetime.now(timezone.utc).isoformat():
        conn.close()
        return jsonify(error="invalid or expired link"), 400
    conn.execute(
        "UPDATE staff SET password_hash = ?, verified = 1 WHERE id = ?",
        (generate_password_hash(new), row["staff_id"]),
    )
    conn.execute("DELETE FROM staff_verification_tokens WHERE token = ?", (token,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/loyalty/staff/birthday")
def staff_birthday():
    staff, err = _require_staff()
    if err:
        return err
    data = request.get_json(force=True) or {}
    bday = (data.get("birthday") or "").strip()
    if bday and not re.match(r"^\d{4}-\d{2}-\d{2}$", bday):
        return jsonify(error="birthday must be YYYY-MM-DD"), 400
    conn = db()
    conn.execute("UPDATE staff SET birthday = ? WHERE id = ?", (bday, staff["id"]))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.get("/api/loyalty/staff/profile")
def staff_profile():
    staff, err = _require_staff()
    if err:
        return err
    conn = db()
    row = conn.execute(
        "SELECT id, name, email, headshot, kernels, birthday, hire_date,"
        " referral_code, created_at"
        " FROM staff WHERE id = ?",
        (staff["id"],),
    ).fetchone()
    history = conn.execute(
        "SELECT kernels, reason, ref, created_at FROM staff_kernel_transactions"
        " WHERE staff_id = ? ORDER BY id DESC LIMIT 50",
        (staff["id"],),
    ).fetchall()
    # Work stats: this employee's customer-facing activity, aggregated from
    # the customer kernel ledger (kernel_transactions.staff_id) — the same
    # queries the admin staff-detail endpoint uses. The My Profile stat
    # boxes (Kernels Credited / Credits Given / Kernels Redeemed /
    # Redemptions) read these fields; without them the endpoint returned
    # no counters at all and the boxes could only ever paint 0.
    credited = conn.execute(
        "SELECT COALESCE(SUM(kernels), 0) AS total, COUNT(*) AS n"
        " FROM kernel_transactions WHERE staff_id = ? AND kernels > 0",
        (staff["id"],),
    ).fetchone()
    redeemed = conn.execute(
        "SELECT COALESCE(SUM(-kernels), 0) AS total, COUNT(*) AS n"
        " FROM kernel_transactions WHERE staff_id = ? AND kernels < 0",
        (staff["id"],),
    ).fetchone()
    staff_rewards = conn.execute(
        "SELECT code, reward_type, created_at FROM loyalty_rewards"
        " WHERE staff_id = ? AND used = 0 ORDER BY created_at DESC",
        (staff["id"],),
    ).fetchall()
    staff_gift_cards = conn.execute(
        "SELECT code, amount_cents, balance_cents, created_at FROM gift_cards"
        " WHERE stripe_session_id = ? AND active = 1 AND balance_cents > 0"
        " ORDER BY created_at DESC",
        (f"staff:{staff['id']}",),
    ).fetchall()
    conn.close()
    work_stats = {
        "kernels_credited": credited["total"] or 0,
        "credit_count": credited["n"] or 0,
        "kernels_redeemed": redeemed["total"] or 0,
        "redeem_count": redeemed["n"] or 0,
    }
    return jsonify(
        id=row["id"], name=row["name"], email=row["email"],
        headshot=row["headshot"] or "", kernels=row["kernels"] or 0,
        staff_kernels=row["kernels"] or 0,
        birthday=row["birthday"] or "", hire_date=row["hire_date"] or "",
        referral_code=row["referral_code"] or "",
        created_at=row["created_at"],
        # The four work-stat counters, top-level AND nested under stats /
        # work_stats so every client payload shape reads the same numbers.
        kernels_credited=work_stats["kernels_credited"],
        credit_count=work_stats["credit_count"],
        kernels_redeemed=work_stats["kernels_redeemed"],
        redeem_count=work_stats["redeem_count"],
        stats=work_stats,
        work_stats=work_stats,
        available_rewards=[
            {"code": rw["code"],
             "label": STAFF_REWARD_TIERS.get(rw["reward_type"], {}).get("label", rw["reward_type"]),
             "created_at": rw["created_at"]}
            for rw in staff_rewards
        ],
        available_gift_cards=[
            {"code": g["code"], "amount_cents": g["amount_cents"],
             "balance_cents": g["balance_cents"], "created_at": g["created_at"]}
            for g in staff_gift_cards
        ],
        reward_tiers={k: v["kernels"] for k, v in STAFF_REWARD_TIERS.items()},
        reward_labels={k: v["label"] for k, v in STAFF_REWARD_TIERS.items()},
        history=[
            {"kernels": h["kernels"], "reason": h["reason"], "ref": h["ref"] or "",
             "note": h["ref"] or "",
             "created_at": h["created_at"]}
            for h in history
        ],
    )

@app.post("/api/loyalty/staff/password")
def staff_change_password():
    staff, err = _require_staff()
    if err:
        return err
    data = request.get_json(force=True) or {}
    current = data.get("current_password") or ""
    new = data.get("new_password") or ""
    if len(new) < 8:
        return jsonify(error="new password must be at least 8 characters"), 400
    conn = db()
    row = conn.execute(
        "SELECT password_hash FROM staff WHERE id = ?", (staff["id"],)
    ).fetchone()
    if not row or not check_password_hash(row["password_hash"], current):
        conn.close()
        return jsonify(error="current password is incorrect"), 401
    conn.execute(
        "UPDATE staff SET password_hash = ? WHERE id = ?",
        (generate_password_hash(new), staff["id"]),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/loyalty/staff/headshot")
def staff_headshot():
    staff, err = _require_staff()
    if err:
        return err
    data = request.get_json(force=True) or {}
    img = (data.get("headshot") or "").strip()
    # Accept a data URL (jpeg/png/webp), cap at ~500KB.
    if not img.startswith("data:image/"):
        return jsonify(error="upload an image file"), 400
    if len(img) > 700_000:
        return jsonify(error="image is too large — keep it under 500KB"), 400
    conn = db()
    conn.execute("UPDATE staff SET headshot = ? WHERE id = ?", (img, staff["id"]))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/loyalty/staff/signup-member")
def staff_signup_member():
    """Staff registers a new customer in person. Auto-credits the staff 1 kernel."""
    staff, err = _require_staff()
    if err:
        return err
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""
    if not name:
        return jsonify(error="please enter the customer's name"), 400
    if not EMAIL_RE.match(email):
        return jsonify(error="please enter a valid email address"), 400
    if len(password) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    conn = db()
    existing = conn.execute(
        "SELECT id, active FROM users WHERE email = ?", (email,)
    ).fetchone()
    if existing and existing["active"]:
        conn.close()
        return jsonify(error="an account with this email already exists"), 409
    if existing:
        conn.execute("DELETE FROM users WHERE id = ?", (existing["id"],))
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO users (email, name, password_hash, verified, created_at)"
        " VALUES (?, ?, ?, 0, ?)",
        (email, name, generate_password_hash(password), now),
    )
    user_id = cur.lastrowid
    token = secrets.token_urlsafe(32)
    expires = (datetime.now(timezone.utc) + timedelta(hours=24)).isoformat()
    conn.execute(
        "INSERT INTO verification_tokens (token, user_id, expires_at) VALUES (?, ?, ?)",
        (token, user_id, expires),
    )
    # Auto-credit the staff member 1 kernel for the signup.
    _credit_staff_kernels(conn, staff["id"], 1, "member_signup", ref=email)
    conn.commit()
    staff_kernels = conn.execute(
        "SELECT kernels FROM staff WHERE id = ?", (staff["id"],)
    ).fetchone()["kernels"]
    conn.close()
    verify_url = f"{SITE_URL}/#verify?token={token}"
    try:
        send_email(email, "Verify your Pop-A-Licious account",
                   f"Hi {name},\n\nPlease verify your account:\n{verify_url}\n")
    except Exception:
        pass
    return jsonify(ok=True, staff_kernels=staff_kernels)

@app.post("/api/loyalty/staff/redeem")
def staff_redeem():
    """Staff redeems their own kernels for an employee reward."""
    staff, err = _require_staff()
    if err:
        return err
    data = request.get_json(force=True) or {}
    reward_type = (data.get("reward_type") or "").strip()
    tier = STAFF_REWARD_TIERS.get(reward_type)
    if not tier:
        return jsonify(error="unknown reward"), 400
    conn = db()
    srow = conn.execute(
        "SELECT name, email, kernels FROM staff WHERE id = ?", (staff["id"],)
    ).fetchone()
    if not srow or (srow["kernels"] or 0) < tier["kernels"]:
        conn.close()
        return jsonify(error="not enough Kernels"), 402
    now = datetime.now(timezone.utc).isoformat()
    kind = tier["kind"]
    if kind == "giftcard_choice":
        # Employee picks which gift card they want — fulfilled by DJ/Matt.
        choice = (data.get("gift_card_choice") or "").strip()[:80]
        if not choice:
            conn.close()
            return jsonify(error="please choose which gift card you want"), 400
        # Visa prepaid cards start at $25 and DoorDash digital cards start at $15 —
        # neither is available for the $10 tier.
        if tier.get("amount_cents", 0) < 2500 and "visa" in choice.lower():
            conn.close()
            return jsonify(error="Visa prepaid cards start at $25 — please pick"
                                  " another gift card for the $10 reward"), 400
        if tier.get("amount_cents", 0) < 1500 and "doordash" in choice.lower():
            conn.close()
            return jsonify(error="DoorDash gift cards start at $15 — please pick"
                                  " another gift card for the $10 reward"), 400
        code = "GC-" + secrets.token_hex(3).upper()
        _credit_staff_kernels(conn, staff["id"], -tier["kernels"], "redemption",
                              ref=f"{code} ({choice})")
        conn.commit()
        detail = {"claim_code": code, "gift_card_choice": choice,
                  "note": f"Show this claim code to DJ or Matt to receive your"
                          f" {tier['label']} — {choice}."}
    elif kind == "merch":
        # Claimed in person from DJ/Matt — claim ticket for tracking.
        code = "MERCH-" + secrets.token_hex(3).upper()
        _credit_staff_kernels(conn, staff["id"], -tier["kernels"], "redemption",
                              ref=code)
        conn.commit()
        detail = {"claim_code": code,
                  "note": "Show this claim code to DJ or Matt to pick your merch item."}
    else:
        # Popcorn rewards work in the store checkout like customer rewards.
        code = _new_reward_code()
        _credit_staff_kernels(conn, staff["id"], -tier["kernels"], "redemption",
                              ref=code)
        conn.execute(
            "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent,"
            " created_at, staff_id) VALUES (0, ?, ?, ?, ?, ?)",
            (reward_type, code, tier["kernels"], now, staff["id"]),
        )
        conn.commit()
        detail = {"reward_code": code,
                  "note": "Use this code in the store checkout discount field."}
    balance = conn.execute(
        "SELECT kernels FROM staff WHERE id = ?", (staff["id"],)
    ).fetchone()["kernels"]
    conn.close()
    return jsonify(ok=True, label=tier["label"], balance=balance,
                   kind=kind, **detail)

# ---------------- analytics: tracking (public, no auth) ----------------

@app.post("/api/track/visit")
def track_visit():
    """Log a site visit. Body: {session_id?, path?}. Throttled client-side."""
    data = request.get_json(force=True) or {}
    conn = db()
    conn.execute(
        "INSERT INTO site_visits (session_id, path, created_at) VALUES (?, ?, ?)",
        ((data.get("session_id") or "")[:64], (data.get("path") or "")[:120],
         datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/track/cart")
def track_cart():
    """Log a cart snapshot for abandonment tracking."""
    data = request.get_json(force=True) or {}
    try:
        item_count = int(data.get("item_count") or 0)
    except (TypeError, ValueError):
        item_count = 0
    if item_count <= 0:
        return jsonify(ok=True)
    conn = db()
    conn.execute(
        "INSERT INTO cart_events (session_id, email, items_summary, item_count, created_at)"
        " VALUES (?, ?, ?, ?, ?)",
        ((data.get("session_id") or "")[:64], (data.get("email") or "").strip().lower()[:120],
         (data.get("items_summary") or "")[:500], item_count,
         datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True)

def abandoned_cart_email_html(items, subtotal_cents):
    dollars = lambda c: f"${c / 100:,.2f}"
    rows = "".join(
        f"<tr><td style=\"padding:6px 10px;border-bottom:1px solid #eee;\">{html.escape(str(it.get('name') or 'Popcorn'))}</td>"
        f"<td style=\"padding:6px 10px;border-bottom:1px solid #eee;text-align:center;\">{int(it.get('quantity') or 1)}</td>"
        f"<td style=\"padding:6px 10px;border-bottom:1px solid #eee;text-align:right;\">{dollars(int(it.get('amount_cents') or 0) * int(it.get('quantity') or 1))}</td></tr>"
        for it in items
    )
    checkout_url = SITE_URL + "/#shop"
    return f"""\
<html><body style="font-family: Arial, sans-serif; line-height: 1.6; color: #333;">
<p style="text-align:center;"><img src="https://pop-a-licious.com/logo.png" alt="Pop-A-Licious" style="max-width:220px;"></p>
<p>Hi there,</p>
<p>You left popcorn in your cart! &#x1F37F; Your Pop-A-Licious favorites are still waiting for you:</p>
<table style="border-collapse:collapse;width:100%;max-width:480px;">
<tr><th style="text-align:left;padding:6px 10px;">Item</th><th style="padding:6px 10px;">Qty</th><th style="text-align:right;padding:6px 10px;">Price</th></tr>
{rows}
<tr><td colspan="2" style="padding:8px 10px;"><strong>Subtotal</strong></td><td style="padding:8px 10px;text-align:right;"><strong>{dollars(subtotal_cents)}</strong></td></tr>
</table>
<p>Psst — orders of $50 or more ship FREE with code <strong>FREESHIP50</strong>.</p>
<p style="text-align:center;"><a href="{checkout_url}" style="display:inline-block;background:#e63946;color:#ffffff;text-decoration:none;padding:14px 28px;border-radius:8px;font-weight:bold;">Complete Your Order</a></p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>*It&rsquo;s Not Just Butter &amp; Salt!</em> &#x1F37F;</p>
<p style="font-size:12px;color:#888;">You received this one-time reminder because you entered your email at checkout on pop-a-licious.com. We only send this reminder once per cart. If you no longer wish to receive emails from Pop-A-Licious, reply to this email with "unsubscribe" and we will remove you from our mailing list.</p>
</body></html>"""


def mark_abandoned_converted(email):
    """Mark any pending abandoned-cart snapshots for an email as converted
    (the customer went on to check out, so no reminder should be sent)."""
    email = (email or "").strip().lower()
    if not email or not EMAIL_RE.match(email):
        return
    try:
        conn = db()
        conn.execute(
            "UPDATE abandoned_carts SET status = 'converted', updated_at = ? WHERE email = ? AND status = 'pending'",
            (datetime.now(timezone.utc).isoformat(), email),
        )
        conn.commit()
        conn.close()
    except Exception:
        pass


@app.post("/api/cart/abandoned")
def save_abandoned_cart():
    """Save (or refresh) the pending abandoned-cart snapshot for an email.

    Body: { email, session_id?, items: [{name, amount_cents, quantity}],
            subtotal_cents? }
    One pending snapshot per email: repeat saves update the items and the
    updated_at timestamp, which is what the 2-hour inactivity window keys
    off. A snapshot already emailed (status 'sent') is never revived.
    """
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    if not EMAIL_RE.match(email):
        return jsonify(error="valid email required"), 400
    raw_items = data.get("items")
    if not isinstance(raw_items, list) or not raw_items:
        return jsonify(ok=True)
    items = []
    item_count = 0
    subtotal = 0
    for raw in raw_items[:50]:
        if not isinstance(raw, dict):
            continue
        try:
            qty = max(1, min(999, int(raw.get("quantity") or 1)))
            cents = max(0, int(raw.get("amount_cents") or 0))
        except (TypeError, ValueError):
            continue
        name = str(raw.get("name") or "Popcorn")[:120]
        items.append({"name": name, "quantity": qty, "amount_cents": cents})
        item_count += qty
        subtotal += qty * cents
    if not items:
        return jsonify(ok=True)
    try:
        provided_subtotal = int(data.get("subtotal_cents"))
    except (TypeError, ValueError):
        provided_subtotal = subtotal
    if provided_subtotal > 0:
        subtotal = provided_subtotal
    summary = ", ".join(f"{it['quantity']}x {it['name']}" for it in items)[:500]
    now = datetime.now(timezone.utc).isoformat()
    conn = db()
    existing = conn.execute(
        "SELECT id FROM abandoned_carts WHERE email = ? AND status = 'pending' ORDER BY id DESC LIMIT 1",
        (email,),
    ).fetchone()
    if existing:
        conn.execute(
            "UPDATE abandoned_carts SET session_id = ?, items_json = ?, items_summary = ?, item_count = ?, subtotal_cents = ?, updated_at = ? WHERE id = ?",
            ((data.get("session_id") or "")[:64], json.dumps(items), summary, item_count, subtotal, now, existing["id"]),
        )
    else:
        conn.execute(
            "INSERT INTO abandoned_carts (email, session_id, items_json, items_summary, item_count, subtotal_cents, status, created_at, updated_at)"
            " VALUES (?, ?, ?, ?, ?, ?, 'pending', ?, ?)",
            (email, (data.get("session_id") or "")[:64], json.dumps(items), summary, item_count, subtotal, now, now),
        )
    conn.commit()
    conn.close()
    return jsonify(ok=True)


@app.post("/api/cart/abandoned/run")
def abandoned_cart_run():
    """Cron: email customers whose saved cart has been inactive for 2+ hours.

    Header X-Cron-Secret must equal the CRON_SECRET env var
    (503 when CRON_SECRET is not configured). Each pending cart is emailed
    exactly once: the row is marked 'sent' before/after a successful send
    and is never picked up again.
    """
    if not CRON_SECRET:
        return jsonify(error="cron is not configured"), 503
    if request.headers.get("X-Cron-Secret", "") != CRON_SECRET:
        return jsonify(error="forbidden"), 403
    cutoff = (datetime.now(timezone.utc) - timedelta(hours=2)).isoformat()
    conn = db()
    rows = conn.execute(
        "SELECT * FROM abandoned_carts WHERE status = 'pending' AND updated_at <= ? ORDER BY updated_at ASC LIMIT 200",
        (cutoff,),
    ).fetchall()
    sent = skipped = 0
    for row in rows:
        try:
            items = json.loads(row["items_json"] or "[]")
        except (TypeError, ValueError):
            items = []
        if not items:
            conn.execute("UPDATE abandoned_carts SET status = 'converted' WHERE id = ?", (row["id"],))
            skipped += 1
            continue
        try:
            send_email(
                row["email"],
                "You left popcorn in your cart 🍿",
                abandoned_cart_email_html(items, int(row["subtotal_cents"] or 0)),
            )
        except Exception:
            # Leave the row pending so the next cron run retries it.
            skipped += 1
            continue
        conn.execute(
            "UPDATE abandoned_carts SET status = 'sent', sent_at = ? WHERE id = ?",
            (datetime.now(timezone.utc).isoformat(), row["id"]),
        )
        sent += 1
    conn.commit()
    conn.close()
    return jsonify(ok=True, sent=sent, skipped=skipped)


@app.post("/api/subscriptions/request")
def subscription_request():
    """Log a Subscribe & Save request (in addition to the email the site sends)."""
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    if not EMAIL_RE.match(email):
        return jsonify(error="valid email required"), 400
    conn = db()
    conn.execute(
        "INSERT INTO subscription_requests (email, name, config, created_at)"
        " VALUES (?, ?, ?, ?)",
        (email, (data.get("name") or "")[:120], (data.get("config") or "")[:500],
         datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True)

# ---------------- analytics: admin queries ----------------

def _period_key(group):
    # SQLite expression extracting the day/month/year bucket from ISO created_at.
    if group == "month":
        return "substr(created_at, 1, 7)"
    if group == "year":
        return "substr(created_at, 1, 4)"
    return "substr(created_at, 1, 10)"  # day

def _time_series(conn, table, group, value_expr="COUNT(*)", limit=365):
    key = _period_key(group)
    rows = conn.execute(
        f"SELECT {key} AS period, {value_expr} AS value FROM {table}"
        f" GROUP BY period ORDER BY period DESC LIMIT ?",
        (limit,),
    ).fetchall()
    return [{"period": r["period"], "value": r["value"]} for r in rows]

def _parse_flavor_qty(items_summary):
    """Parse '2x Alien Mix, 1x Caramel' into {flavor: qty}."""
    out = {}
    for part in (items_summary or "").split(","):
        part = part.strip()
        m = re.match(r"^(\d+)\s*x\s*(.+)$", part, re.IGNORECASE)
        if m:
            out[m.group(2).strip()] = out.get(m.group(2).strip(), 0) + int(m.group(1))
    return out

@app.get("/api/admin/analytics")
def admin_analytics():
    """Time-series analytics for the admin dashboard.
    Params: group=day|month|year (default day)."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    group = (request.args.get("group") or "day").strip()
    if group not in ("day", "month", "year"):
        group = "day"
    conn = db()
    data = {
        "sales": _time_series(conn, "orders", group, "COALESCE(SUM(amount_total_cents), 0)"),
        "orders": _time_series(conn, "orders", group),
        "visits": _time_series(conn, "site_visits", group, "COUNT(DISTINCT session_id)"),
        "signups": _time_series(conn, "users", group),
        "rewards_members": _time_series(
            conn,
            "(SELECT user_id, MIN(created_at) AS created_at FROM kernel_transactions GROUP BY user_id)",
            group),
        "promo_uses": _time_series(conn, "promo_redemptions", group),
        "subscriptions": _time_series(conn, "subscription_requests", group),
        "abandoned_carts": _time_series(
            conn,
            "(SELECT created_at FROM cart_events WHERE ordered = 0"
            " AND created_at < datetime('now', '-2 hours'))",
            group),
        "gift_cards": _time_series(conn, "gift_cards", group),
        "gift_card_revenue": _time_series(conn, "gift_cards", group,
                                          "COALESCE(SUM(amount_cents), 0)"),
    }
    # Variety packs: count orders whose items mention a pack.
    key = _period_key(group)
    pack_rows = conn.execute(
        f"SELECT {key} AS period,"
        " SUM(CASE WHEN lower(items_summary) LIKE '%3-pack%' THEN 1 ELSE 0 END) AS packs3,"
        " SUM(CASE WHEN lower(items_summary) LIKE '%6-pack%' THEN 1 ELSE 0 END) AS packs6"
        " FROM orders GROUP BY period ORDER BY period DESC LIMIT 365",
    ).fetchall()
    data["variety_packs"] = [
        {"period": r["period"], "packs_3": r["packs3"], "packs_6": r["packs6"]}
        for r in pack_rows
    ]
    conn.close()
    return jsonify(data)

@app.get("/api/admin/flavor-sales")
def admin_flavor_sales():
    """Per-flavor unit sales time series. Params: group=day|month|year, flavor? (omit for all)."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    group = (request.args.get("group") or "day").strip()
    if group not in ("day", "month", "year"):
        group = "day"
    want = (request.args.get("flavor") or "").strip().lower()
    conn = db()
    rows = conn.execute(
        "SELECT items_summary, created_at FROM orders ORDER BY created_at DESC LIMIT 5000"
    ).fetchall()
    conn.close()
    buckets = {}
    for r in rows:
        created = r["created_at"] or ""
        period = created[:10] if group == "day" else created[:7] if group == "month" else created[:4]
        for flavor, qty in _parse_flavor_qty(r["items_summary"]).items():
            if want and flavor.lower() != want:
                continue
            b = buckets.setdefault(period, {})
            b[flavor] = b.get(flavor, 0) + qty
    series = [
        {"period": p, "flavors": buckets[p]}
        for p in sorted(buckets, reverse=True)[:365]
    ]
    return jsonify(series=series)

@app.post("/api/admin/customers/<int:customer_id>/deactivate")
def admin_deactivate_customer(customer_id):
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    if customer_id == user["id"]:
        return jsonify(error="you cannot deactivate your own account"), 400
    conn = db()
    conn.execute("UPDATE users SET active = 0 WHERE id = ?", (customer_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/admin/customers/<int:customer_id>/activate")
def admin_activate_customer(customer_id):
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    conn.execute("UPDATE users SET active = 1 WHERE id = ?", (customer_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.get("/api/admin/orders/<path:order_id>")
def admin_order_detail(order_id):
    """Full detail for one order. Backfills name/address from Stripe if blank."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    # Accept either the Stripe/PayPal session ID or the friendly order number.
    if order_id.isdigit():
        r = conn.execute(
            "SELECT id, stripe_session_id, email, customer_name, shipping_address,"
            " items_summary, amount_total_cents, gift_card_code,"
            " gift_card_discount_cents, promo_code, reward_code, total_qty,"
            " shippo_label_url, shippo_tracking_number, shippo_label_created_at, created_at"
            " FROM orders WHERE id = ?",
            (int(order_id) - 1000,),
        ).fetchone()
    else:
        r = conn.execute(
            "SELECT id, stripe_session_id, email, customer_name, shipping_address,"
            " items_summary, amount_total_cents, gift_card_code,"
            " gift_card_discount_cents, promo_code, reward_code, total_qty,"
            " shippo_label_url, shippo_tracking_number, shippo_label_created_at, created_at"
            " FROM orders WHERE stripe_session_id = ?",
            (order_id,),
        ).fetchone()
    if not r:
        conn.close()
        return jsonify(error="order not found"), 404
    name = r["customer_name"] or ""
    address = r["shipping_address"] or ""
    stripe_id = r["stripe_session_id"]
    # Backfill from Stripe for orders placed before the detail fields existed.
    if (not name or not address) and not stripe_id.startswith("paypal:"):
        try:
            session = stripe.checkout.Session.retrieve(stripe_id)
            details = session.get("customer_details") or {}
            if not name:
                name = details.get("name") or ""
            if not address:
                addr = details.get("address") or {}
                parts = [addr.get("line1", ""), addr.get("line2", ""),
                         addr.get("city", ""), addr.get("state", ""),
                         addr.get("postal_code", ""), addr.get("country", "")]
                address = ", ".join(p for p in parts if p)
            if name or address:
                conn.execute(
                    "UPDATE orders SET customer_name = ?, shipping_address = ?"
                    " WHERE stripe_session_id = ?",
                    (name, address, stripe_id),
                )
                conn.commit()
        except Exception:
            pass
    conn.close()
    return jsonify(
        id=r["stripe_session_id"], order_number=1000 + r["id"],
        email=r["email"] or "",
        customer_name=name, shipping_address=address,
        items=r["items_summary"] or "",
        total_cents=r["amount_total_cents"] or 0,
        gift_card_code=r["gift_card_code"] or "",
        gift_card_discount_cents=r["gift_card_discount_cents"] or 0,
        promo_code=r["promo_code"] or "", reward_code=r["reward_code"] or "",
        total_qty=r["total_qty"] or 0,
        shippo_label_url=r["shippo_label_url"] or "",
        shippo_tracking_number=r["shippo_tracking_number"] or "",
        shippo_label_created_at=r["shippo_label_created_at"] or "",
        payment_method="PayPal" if r["stripe_session_id"].startswith("paypal:") else "Stripe",
        created_at=r["created_at"],
    )

@app.get("/api/admin/orders/<order_id>/label")
def admin_order_label(order_id):
    """Return the Shippo label info for an order (admin)."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    r = _admin_find_order(conn, order_id)
    conn.close()
    if not r:
        return jsonify(error="order not found"), 404
    return jsonify(
        label_url=r["shippo_label_url"] or "",
        tracking_number=r["shippo_tracking_number"] or "",
        label_created_at=r["shippo_label_created_at"] or "",
    )

@app.post("/api/admin/orders/<order_id>/create-label")
def admin_order_create_label(order_id):
    """Retry Shippo label creation for an order missing one (admin).

    Rebuilds the destination address from the best available source:
    subscription record (sub_ orders), Stripe session shipping details,
    or the stored shipping address string as a last resort.
    """
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    r = _admin_find_order(conn, order_id)
    if not r:
        conn.close()
        return jsonify(error="order not found"), 404
    if r["shippo_label_url"]:
        conn.close()
        return jsonify(ok=True, already=True,
                       label_url=r["shippo_label_url"],
                       tracking_number=r["shippo_tracking_number"] or "")
    stripe_id = r["stripe_session_id"] or ""
    total_qty = r["total_qty"] or 0
    address_to = None

    # sub_ orders: the subscription holds the structured address.
    if stripe_id.startswith("sub_"):
        ren = conn.execute(
            "SELECT subscription_id FROM subscription_renewals WHERE order_id = ?",
            (r["id"],)).fetchone()
        if ren:
            sub = conn.execute(
                "SELECT ship_name, ship_street, ship_city, ship_state, ship_zip"
                " FROM subscriptions WHERE id = ?",
                (ren["subscription_id"],)).fetchone()
            if sub:
                address_to = _shippo_address_to(
                    name=sub["ship_name"] or "", street1=sub["ship_street"] or "",
                    city=sub["ship_city"] or "", state=sub["ship_state"] or "",
                    zip_code=sub["ship_zip"] or "")

    # Stripe orders: re-fetch shipping details from the Stripe session.
    if address_to is None and not stripe_id.startswith("paypal:"):
        try:
            session = stripe.checkout.Session.retrieve(stripe_id)
            ship = session.get("shipping_details") or {}
            saddr = ship.get("address") or {}
            address_to = _shippo_address_to(
                name=ship.get("name") or r["customer_name"] or "",
                street1=saddr.get("line1", ""), street2=saddr.get("line2", ""),
                city=saddr.get("city", ""), state=saddr.get("state", ""),
                zip_code=saddr.get("postal_code", ""),
                country=saddr.get("country", "US"))
        except Exception:
            address_to = None

    # Last resort: parse the stored "line1, line2, city, state, zip, country"
    # shipping address string.
    if address_to is None:
        parts = [p.strip() for p in (r["shipping_address"] or "").split(",")]
        if len(parts) >= 5:
            address_to = _shippo_address_to(
                name=parts[0], street1="",
                city=parts[-4], state=parts[-3], zip_code=parts[-2],
                country=parts[-1] if len(parts) >= 6 else "US")
    if address_to is None:
        conn.close()
        return jsonify(error="could not determine the shipping address"), 400

    label_url, tracking_number = _create_shippo_label(
        address_to, total_qty, order_ref=stripe_id)
    if not label_url:
        conn.close()
        return jsonify(error="Shippo could not create a label for this order"), 502
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        "UPDATE orders SET shippo_label_url = ?, shippo_tracking_number = ?,"
        " shippo_label_created_at = ? WHERE id = ?",
        (label_url, tracking_number or "", now, r["id"]))
    conn.commit()
    conn.close()
    return jsonify(ok=True, label_url=label_url,
                   tracking_number=tracking_number or "")

def _admin_find_order(conn, order_id):
    """Fetch an order row by friendly number or session ID (for admin label endpoints)."""
    if order_id.isdigit():
        return conn.execute(
            "SELECT id, stripe_session_id, customer_name, shipping_address,"
            " total_qty, shippo_label_url, shippo_tracking_number,"
            " shippo_label_created_at FROM orders WHERE id = ?",
            (int(order_id) - 1000,)).fetchone()
    return conn.execute(
        "SELECT id, stripe_session_id, customer_name, shipping_address,"
        " total_qty, shippo_label_url, shippo_tracking_number,"
        " shippo_label_created_at FROM orders WHERE stripe_session_id = ?",
        (order_id,)).fetchone()

@app.get("/api/admin/orders")
def admin_orders():
    """Full order list for admins, with search. Params: search?, limit?, offset?"""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    search = (request.args.get("search") or "").strip()
    try:
        limit = min(max(int(request.args.get("limit") or 50), 1), 200)
        offset = max(int(request.args.get("offset") or 0), 0)
    except (TypeError, ValueError):
        limit, offset = 50, 0
    conn = db()
    params = []
    where = ""
    if search:
        where = "WHERE lower(o.email) LIKE ? OR lower(o.items_summary) LIKE ? OR lower(o.stripe_session_id) LIKE ?"
        like = f"%{search.lower()}%"
        params = [like, like, like]
    total = conn.execute(
        f"SELECT COUNT(*) AS c FROM orders o {where}", params).fetchone()["c"]
    rows = conn.execute(
        "SELECT o.id, o.stripe_session_id, o.email, o.customer_name, o.shipping_address,"
        " o.items_summary, o.amount_total_cents,"
        " o.gift_card_code, o.gift_card_discount_cents,"
        " o.promo_code, o.reward_code, o.is_demo, o.created_at"
        f" FROM orders o {where} ORDER BY o.id DESC LIMIT ? OFFSET ?",
        params + [limit, offset],
    ).fetchall()
    conn.close()
    return jsonify(total=total, orders=[
        {"id": r["stripe_session_id"], "order_number": 1000 + r["id"],
         "email": r["email"],
         "customer_name": r["customer_name"] or "",
         "shipping_address": r["shipping_address"] or "",
         "items": r["items_summary"] or "",
         "total_cents": r["amount_total_cents"] or 0,
         "gift_card_code": r["gift_card_code"] or "",
         "gift_card_discount_cents": r["gift_card_discount_cents"] or 0,
         "promo_code": r["promo_code"] or "", "reward_code": r["reward_code"] or "",
         "is_demo": bool(r["is_demo"]),
         "created_at": r["created_at"]}
        for r in rows
    ])

@app.get("/api/admin/gift-cards")
def admin_gift_card_list():
    """All gift cards for the admin dashboard drill-down."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    rows = conn.execute(
        "SELECT code, amount_cents, balance_cents, purchaser_name, purchaser_email,"
        " recipient_name, recipient_email, active, created_at"
        " FROM gift_cards ORDER BY created_at DESC LIMIT 500"
    ).fetchall()
    conn.close()
    return jsonify(gift_cards=[
        {"code": r["code"], "amount_cents": r["amount_cents"],
         "balance_cents": r["balance_cents"], "purchaser_name": r["purchaser_name"],
         "purchaser_email": r["purchaser_email"], "recipient_name": r["recipient_name"],
         "recipient_email": r["recipient_email"], "active": bool(r["active"]),
         "created_at": r["created_at"]}
        for r in rows
    ])

@app.get("/api/admin/customers")
def admin_customers():
    """List of everyone with an account."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    rows = conn.execute(
        "SELECT u.id, u.name, u.email, u.verified, u.birthday, u.active, u.created_at,"
        " COALESCE((SELECT SUM(kernels) FROM kernel_transactions k WHERE k.user_id = u.id), 0) AS kernels,"
        " (SELECT COUNT(*) FROM orders o WHERE o.email = u.email) AS orders"
        " FROM users u WHERE u.active = 1 ORDER BY u.created_at DESC LIMIT 1000"
    ).fetchall()
    conn.close()
    return jsonify(customers=[
        {"id": r["id"], "name": r["name"], "email": r["email"],
         "verified": bool(r["verified"]), "birthday": r["birthday"] or "",
         "active": bool(r["active"]),
         "kernels": r["kernels"], "orders": r["orders"], "created_at": r["created_at"]}
        for r in rows
    ])

# ---------------- admin: manage staff logins ----------------

@app.post("/api/admin/staff")
def admin_create_staff():
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    name = (data.get("name") or "").strip()
    password = data.get("password") or ""
    if not EMAIL_RE.match(email):
        return jsonify(error="valid email required"), 400
    if len(password) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    conn = db()
    # A deactivated staff email can be reused: reactivate the old row so their
    # Kernel balance, history, and referral code are preserved (points never reset).
    old = conn.execute(
        "SELECT id, referral_code FROM staff WHERE email = ? AND active = 0", (email,)
    ).fetchone()
    if old:
        conn.execute(
            "UPDATE staff SET name = ?, password_hash = ?, verified = 0,"
            " active = 1 WHERE id = ?",
            (name or email.split("@")[0], generate_password_hash(password), old["id"]),
        )
        staff_id = old["id"]
        vtoken = secrets.token_urlsafe(32)
        vexpires = (datetime.now(timezone.utc) + timedelta(hours=48)).isoformat()
        conn.execute(
            "INSERT INTO staff_verification_tokens (token, staff_id, expires_at) VALUES (?, ?, ?)",
            (vtoken, staff_id, vexpires),
        )
        conn.commit()
        conn.close()
        verify_url = f"{SITE_URL}/#staff-verify?token={vtoken}"
        try:
            send_email(
                email,
                "Your Pop-A-Licious staff account",
                f"Hi {name or 'there'},\n\nYour staff account has been reactivated.\n"
                f"Click below to verify your account and set your password:\n{verify_url}\n\n"
                f"This link expires in 48 hours.\n",
            )
        except Exception:
            pass
        return jsonify(ok=True, reactivated=True)
    try:
        ref_code = "STF-" + secrets.token_hex(3).upper()
        cur = conn.execute(
            "INSERT INTO staff (email, name, password_hash, referral_code, verified, created_at) VALUES (?, ?, ?, ?, 0, ?)",
            (email, name or email.split("@")[0], generate_password_hash(password),
             ref_code, datetime.now(timezone.utc).isoformat()),
        )
        staff_id = cur.lastrowid
        # Verification token for the staff welcome email.
        vtoken = secrets.token_urlsafe(32)
        vexpires = (datetime.now(timezone.utc) + timedelta(hours=48)).isoformat()
        conn.execute(
            "INSERT INTO staff_verification_tokens (token, staff_id, expires_at) VALUES (?, ?, ?)",
            (vtoken, staff_id, vexpires),
        )
        conn.commit()
    except sqlite3.IntegrityError:
        conn.close()
        return jsonify(error="that staff email already exists"), 409
    conn.close()
    verify_url = f"{SITE_URL}/#staff-verify?token={vtoken}"
    try:
        send_email(
            email,
            "Your Pop-A-Licious staff account",
            f"Hi {name or 'there'},\n\nYour staff account has been created.\n"
            f"Click below to verify your account and set your password:\n{verify_url}\n\n"
            f"This link expires in 48 hours.\n",
        )
    except Exception:
        pass
    return jsonify(ok=True)

# ---------------- Marketing emails (promos + merch drops) ----------------
# Audience = deduplicated: active+verified users + order emails (Stripe +
# PayPal), minus unsubscribes. Admin-gated sends. Every email carries a
# one-click unsubscribe link (HMAC-signed) + the business address.

MARKETING_FROM = os.environ.get("EMAIL_FROM", "Pop-A-Licious <noreply@pop-a-licious.com>")
MARKETING_ADDRESS_HTML = ("Pop-A-Licious, 2013 Angel Falls Dr., Henderson, NV 89074")

def _unsub_token(email):
    sig = hmac.new(RESEND_API_KEY.encode(), email.lower().encode(), hashlib.sha256).digest()
    return base64.urlsafe_b64encode(sig).decode().rstrip("=")

def _verify_unsub_token(email, token):
    try:
        return hmac.compare_digest(_unsub_token(email), token)
    except Exception:
        return False

def _marketing_audience(conn):
    """Deduplicated marketing audience: one email per address."""
    emails = {}
    for row in conn.execute(
            "SELECT email, name FROM users WHERE active = 1 AND verified = 1 AND email != ''"):
        emails[row["email"].lower()] = {"email": row["email"], "name": row["name"] or ""}
    for row in conn.execute(
            "SELECT DISTINCT email FROM orders WHERE email IS NOT NULL AND email != ''"):
        emails.setdefault(row["email"].lower(), {"email": row["email"], "name": ""})
    for row in conn.execute(
            "SELECT DISTINCT email FROM paypal_orders WHERE email IS NOT NULL AND email != ''"):
        emails.setdefault(row["email"].lower(), {"email": row["email"], "name": ""})
    unsub = {r["email"] for r in conn.execute("SELECT email FROM marketing_unsubscribes")}
    return [v for k, v in emails.items() if k not in unsub]

def _marketing_email_html(body_html, email):
    token = _unsub_token(email)
    qs = urlencode({"email": email, "token": token})
    unsub_url = f"https://pop-a-licious.com/api/marketing/unsubscribe?{qs}"
    return f"""{body_html}
<hr style="border:none;border-top:1px solid #ddd;margin:24px 0;">
<p style="font-size:12px;color:#888;">You're receiving this because you're a Pop-A-Licious customer.<br>
<a href="{unsub_url}" style="color:#888;">Unsubscribe</a> &nbsp;|&nbsp; {MARKETING_ADDRESS_HTML}</p>"""

def _send_marketing_batch(batch):
    """batch: list of dicts {to, subject, html}. Uses Resend batch endpoint (max 100)."""
    resp = requests.post(
        "https://api.resend.com/emails/batch",
        headers={"Authorization": f"Bearer {RESEND_API_KEY}", "Content-Type": "application/json"},
        json=[
            {
                "from": MARKETING_FROM,
                "to": [item["to"]],
                "subject": item["subject"],
                "html": item["html"],
                "headers": {"List-Unsubscribe": f"<{item['unsub_url']}>"},
            }
            for item in batch
        ],
        timeout=30,
    )
    resp.raise_for_status()
    return resp.json()

@app.post("/api/admin/marketing/audience")
def admin_marketing_audience():
    """Return the deduplicated marketing audience count (admin preview before sending)."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    audience = _marketing_audience(conn)
    conn.close()
    return jsonify(count=len(audience))

@app.post("/api/admin/marketing/send")
def admin_marketing_send():
    """Send a marketing email to the deduplicated audience. Admin only.
    Body: {name, subject, html_body}. html_body is the inner content; footer
    with unsubscribe + address is appended automatically."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()[:120]
    subject = (data.get("subject") or "").strip()
    html_body = data.get("html_body") or ""
    if not subject or not html_body:
        return jsonify(error="subject and html_body are required"), 400
    conn = db()
    audience = _marketing_audience(conn)
    sent = 0
    for i in range(0, len(audience), 100):
        chunk = audience[i:i + 100]
        batch = []
        for person in chunk:
            email = person["email"]
            token = _unsub_token(email)
            qs = urlencode({"email": email, "token": token})
            unsub_url = f"https://pop-a-licious.com/api/marketing/unsubscribe?{qs}"
            batch.append({
                "to": email,
                "subject": subject,
                "html": _marketing_email_html(html_body, email),
                "unsub_url": unsub_url,
            })
        try:
            _send_marketing_batch(batch)
            sent += len(batch)
        except Exception as e:
            conn.close()
            return jsonify(error=f"send failed after {sent} emails: {e}"), 502
    conn.execute(
        "INSERT INTO marketing_campaigns (name, subject, audience, recipient_count, sent_at)"
        " VALUES (?, ?, 'all', ?, ?)",
        (name, subject, sent, datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True, sent=sent, campaign=name)

@app.get("/api/admin/marketing/campaigns")
def admin_marketing_campaigns():
    """List past marketing campaigns (admin)."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    rows = conn.execute(
        "SELECT id, name, subject, recipient_count, sent_at FROM marketing_campaigns"
        " ORDER BY id DESC LIMIT 50").fetchall()
    conn.close()
    return jsonify(campaigns=[dict(r) for r in rows])

@app.get("/api/marketing/unsubscribe")
def marketing_unsubscribe():
    """One-click unsubscribe (signed link from marketing emails)."""
    email = (request.args.get("email") or "").strip()
    token = request.args.get("token") or ""
    if not email or not _verify_unsub_token(email, token):
        return ("<html><body style='font-family:sans-serif;text-align:center;padding:60px;'>"
                "<h2>Invalid unsubscribe link</h2>"
                "<p>Please use the link from your Pop-A-Licious email.</p></body></html>"), 400
    conn = db()
    conn.execute(
        "INSERT OR IGNORE INTO marketing_unsubscribes (email, created_at) VALUES (?, ?)",
        (email.lower(), datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return ("<html><body style='font-family:sans-serif;text-align:center;padding:60px;'>"
            "<h2>You're unsubscribed</h2>"
            "<p>You won't receive Pop-A-Licious promo or merch emails anymore.</p>"
            "<p><a href='https://pop-a-licious.com'>Back to pop-a-licious.com</a></p></body></html>")

# ---------------- Scheduled marketing campaigns (cron-secret protected) ----------------
# Pre-defined campaigns sent by cron-job.org on the retail calendar dates.
# Body: {"campaign_key": "<key>"} — each key sends once (tracked in
# marketing_campaigns; re-sending the same key is a no-op).

SCHEDULED_CAMPAIGNS = {
    "xmas2026_launch": {
        "name": "Holiday 2026 merch drop + MERRYPOP15",
        "subject": "🎄 Our Holiday Merch Drop Is Here + 15% Off Everything",
        "html_body": """<h2 style="color:#c0392b;">Merry Popmas! 🎄🍿</h2>
<p>Our <strong>Holiday 2026 merch drop</strong> just landed — cozy, festive, and
only here for the season:</p>
<ul>
<li><strong>"Merry Popmas" Hoodie</strong> — $55</li>
<li><strong>"Ugly Sweater" Holiday Tee</strong> — $28</li>
<li><strong>"Pop! Pop! Hooray!" Holiday Mug</strong> — $18</li>
<li><strong>"Popcorn Garland" Holiday Socks</strong> — $16</li>
</ul>
<p>Plus take <strong>15% off everything</strong> with code
<strong style="font-size:18px;">MERRYPOP15</strong> at checkout — now through Dec 26.</p>
<p><a href="https://pop-a-licious.com" style="background:#c0392b;color:#fff;padding:12px 24px;text-decoration:none;border-radius:6px;">Shop the Drop</a></p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>It's Not Just Butter &amp; Salt!</em> 🍿</p>""",
    },
    "xmas2026_blackfriday": {
        "name": "Black Friday 2026 — BLACKPOP25",
        "subject": "🖤 Black Friday: 25% Off Everything — Today Only-ish",
        "html_body": """<h2 style="color:#111;">Black Friday Is Poppin' 🖤🍿</h2>
<p>Our biggest sale of the year: <strong>25% off EVERYTHING</strong> — popcorn,
merch, all of it.</p>
<p>Use code <strong style="font-size:20px;">BLACKPOP25</strong> at checkout.</p>
<p>Sale runs Nov 27 – Nov 29. When it's gone, it's gone.</p>
<p><a href="https://pop-a-licious.com" style="background:#111;color:#fff;padding:12px 24px;text-decoration:none;border-radius:6px;">Shop Black Friday</a></p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>It's Not Just Butter &amp; Salt!</em> 🍿</p>""",
    },
    "xmas2026_cybermonday": {
        "name": "Cyber Monday 2026 — CYBERPOP25",
        "subject": "💻 Cyber Monday: 25% Off Ends Tonight",
        "html_body": """<h2 style="color:#111;">Cyber Monday — Last Call 💻🍿</h2>
<p><strong>25% off EVERYTHING</strong> ends tonight at midnight.</p>
<p>Use code <strong style="font-size:20px;">CYBERPOP25</strong> at checkout.</p>
<p>After tonight, our holiday sale drops back to 15% off — don't miss the big one.</p>
<p><a href="https://pop-a-licious.com" style="background:#111;color:#fff;padding:12px 24px;text-decoration:none;border-radius:6px;">Shop Cyber Monday</a></p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>It's Not Just Butter &amp; Salt!</em> 🍿</p>""",
    },
    "xmas2026_shipping_deadline": {
        "name": "Christmas 2026 shipping deadlines",
        "subject": "🎄 Last Days to Order for Christmas Delivery",
        "html_body": """<h2 style="color:#c0392b;">Don't Miss Christmas Delivery 🎄🍿</h2>
<p>Want Pop-A-Licious under the tree? Here are the last days to order:</p>
<ul>
<li><strong>Merch (hoodies, tees, mugs & more):</strong> order by <strong>Dec 10</strong></li>
<li><strong>Popcorn:</strong> order by <strong>Dec 16</strong></li>
</ul>
<p>After those dates we can't guarantee Christmas delivery — order early!</p>
<p><a href="https://pop-a-licious.com" style="background:#c0392b;color:#fff;padding:12px 24px;text-decoration:none;border-radius:6px;">Order Now</a></p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>It's Not Just Butter &amp; Salt!</em> 🍿</p>""",
    },
    "xmas2026_last_call": {
        "name": "Christmas 2026 last call — popcorn",
        "subject": "⏰ Tomorrow's the Last Day for Christmas Popcorn Delivery",
        "html_body": """<h2 style="color:#c0392b;">Last Call for Christmas Popcorn ⏰🍿</h2>
<p><strong>Tomorrow (Dec 16)</strong> is the last day to order popcorn for
guaranteed Christmas delivery.</p>
<p>Merch orders have closed for Christmas — but popcorn can still make it!</p>
<p>Use code <strong>MERRYPOP15</strong> for 15% off.</p>
<p><a href="https://pop-a-licious.com" style="background:#c0392b;color:#fff;padding:12px 24px;text-decoration:none;border-radius:6px;">Order Popcorn Now</a></p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br><em>It's Not Just Butter &amp; Salt!</em> 🍿</p>""",
    },
}

@app.post("/api/cron/marketing/send")
def cron_marketing_send():
    """Cron: send a pre-defined marketing campaign to the deduplicated audience.

    Header X-Cron-Secret must equal the CRON_SECRET env var.
    Body: {"campaign_key": "<key from SCHEDULED_CAMPAIGNS>"}.
    Each key sends at most once (tracked in marketing_campaigns).
    """
    if not CRON_SECRET:
        return jsonify(error="cron is not configured"), 503
    if request.headers.get("X-Cron-Secret", "") != CRON_SECRET:
        return jsonify(error="forbidden"), 403
    data = request.get_json(force=True) or {}
    key = (data.get("campaign_key") or "").strip()
    campaign = SCHEDULED_CAMPAIGNS.get(key)
    if not campaign:
        return jsonify(error="unknown campaign_key"), 400
    conn = db()
    already = conn.execute(
        "SELECT id FROM marketing_campaigns WHERE name = ?", (campaign["name"],)).fetchone()
    if already:
        conn.close()
        return jsonify(ok=True, sent=0, note="already sent")
    audience = _marketing_audience(conn)
    sent = 0
    for i in range(0, len(audience), 100):
        chunk = audience[i:i + 100]
        batch = []
        for person in chunk:
            email = person["email"]
            qs = urlencode({"email": email, "token": _unsub_token(email)})
            unsub_url = f"https://pop-a-licious.com/api/marketing/unsubscribe?{qs}"
            batch.append({
                "to": email,
                "subject": campaign["subject"],
                "html": _marketing_email_html(campaign["html_body"], email),
                "unsub_url": unsub_url,
            })
        try:
            _send_marketing_batch(batch)
            sent += len(batch)
        except Exception as e:
            conn.close()
            return jsonify(error=f"send failed after {sent} emails: {e}"), 502
    conn.execute(
        "INSERT INTO marketing_campaigns (name, subject, audience, recipient_count, sent_at)"
        " VALUES (?, ?, 'all', ?, ?)",
        (campaign["name"], campaign["subject"], sent, datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True, sent=sent, campaign=campaign["name"])

@app.get("/api/admin/dashboard")
def admin_dashboard():
    """Key site stats for the admin dashboard."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    revenue = conn.execute(
        "SELECT COALESCE(SUM(amount_total_cents), 0) AS s FROM orders").fetchone()["s"]
    total_orders = conn.execute(
        "SELECT COUNT(*) AS c FROM orders").fetchone()["c"]
    orders_today = conn.execute(
        "SELECT COUNT(*) AS c FROM orders WHERE substr(created_at, 1, 10) = date('now')").fetchone()["c"]
    revenue_today = conn.execute(
        "SELECT COALESCE(SUM(amount_total_cents), 0) AS s FROM orders"
        " WHERE substr(created_at, 1, 10) = date('now')").fetchone()["s"]
    gift_cards_sold = conn.execute(
        "SELECT COUNT(*) AS c FROM gift_cards").fetchone()["c"]
    gift_cards_outstanding = conn.execute(
        "SELECT COALESCE(SUM(balance_cents), 0) AS s FROM gift_cards WHERE active = 1").fetchone()["s"]
    members = conn.execute(
        "SELECT COUNT(*) AS c FROM users WHERE verified = 1").fetchone()["c"]
    kernels_issued = conn.execute(
        "SELECT COALESCE(SUM(kernels), 0) AS s FROM kernel_transactions WHERE kernels > 0").fetchone()["s"]
    pending_reviews = conn.execute(
        "SELECT COUNT(*) AS c FROM reviews WHERE approved = 0").fetchone()["c"]
    active_staff = conn.execute(
        "SELECT COUNT(*) AS c FROM staff WHERE active = 1").fetchone()["c"]
    erp_inventory_value = conn.execute(
        "SELECT COALESCE(SUM(l.q * i.avg_cost_cents), 0) AS v FROM"
        " (SELECT item_id, SUM(qty_change) AS q FROM erp_stock_ledger GROUP BY item_id) l"
        " JOIN erp_items i ON i.id = l.item_id").fetchone()["v"]
    erp_open_pos = conn.execute(
        "SELECT COUNT(*) AS c FROM erp_purchase_orders"
        " WHERE status IN ('draft', 'sent', 'partial')").fetchone()["c"]
    recent_orders = conn.execute(
        "SELECT email, items_summary, amount_total_cents, created_at FROM orders"
        " ORDER BY id DESC LIMIT 10").fetchall()
    conn.close()
    return jsonify(
        revenue_cents=revenue, total_orders=total_orders,
        orders_today=orders_today, revenue_today_cents=revenue_today,
        gift_cards_sold=gift_cards_sold,
        gift_cards_outstanding_cents=gift_cards_outstanding,
        loyalty_members=members, kernels_issued=kernels_issued,
        pending_reviews=pending_reviews, active_staff=active_staff,
        inventory_value_cents=int(erp_inventory_value or 0),
        open_purchase_orders=erp_open_pos,
        recent_orders=[
            {"email": r["email"], "items": r["items_summary"] or "",
             "total_cents": r["amount_total_cents"] or 0, "created_at": r["created_at"]}
            for r in recent_orders
        ],
    )

@app.get("/api/admin/fundraising")
def admin_fundraising():
    """Aggregate fundraising stats for the admin dashboard."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    total_raised = conn.execute(
        "SELECT COALESCE(SUM(total_cents), 0) AS s FROM fundraiser_orders"
        " WHERE status = 'paid'").fetchone()["s"]
    total_donations = conn.execute(
        "SELECT COALESCE(SUM(donation_cents + roundup_cents), 0) AS s"
        " FROM fundraiser_orders WHERE status = 'paid'").fetchone()["s"]
    fundraiser_orders = conn.execute(
        "SELECT COUNT(*) AS c FROM fundraiser_orders"
        " WHERE status = 'paid'").fetchone()["c"]
    active_fundraisers = conn.execute(
        "SELECT COUNT(*) AS c FROM fundraisers WHERE status = 'active'").fetchone()["c"]
    completed_fundraisers = conn.execute(
        "SELECT COUNT(*) AS c FROM fundraisers WHERE status != 'active'").fetchone()["c"]
    # Revenue by day for the last 30 days (chart).
    chart = conn.execute(
        "SELECT substr(created_at, 1, 10) AS day,"
        " COALESCE(SUM(total_cents), 0) AS total"
        " FROM fundraiser_orders WHERE status = 'paid'"
        " AND created_at >= date('now', '-30 days')"
        " GROUP BY day ORDER BY day").fetchall()
    conn.close()
    return jsonify(
        total_raised_cents=total_raised,
        total_donations_cents=total_donations,
        fundraiser_orders=fundraiser_orders,
        active_fundraisers=active_fundraisers,
        completed_fundraisers=completed_fundraisers,
        revenue_chart=[{"day": r["day"], "total_cents": r["total"]} for r in chart],
    )

@app.get("/api/admin/staff")
def admin_list_staff():
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    rows = conn.execute(
        "SELECT id, email, name, active, created_at FROM staff"
        " WHERE active = 1 ORDER BY created_at DESC"
    ).fetchall()
    conn.close()
    return jsonify(staff=[
        {"id": r["id"], "email": r["email"], "name": r["name"],
         "active": bool(r["active"]), "created_at": r["created_at"]}
        for r in rows
    ])

@app.post("/api/admin/staff/<int:staff_id>/deactivate")
def admin_deactivate_staff(staff_id):
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    conn.execute("UPDATE staff SET active = 0 WHERE id = ?", (staff_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/admin/staff/<int:staff_id>/activate")
def admin_activate_staff(staff_id):
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    conn.execute("UPDATE staff SET active = 1 WHERE id = ?", (staff_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/admin/staff/<int:staff_id>/update")
def admin_update_staff(staff_id):
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    data = request.get_json(force=True) or {}
    hire_date = (data.get("hire_date") or "").strip()
    if hire_date and not re.match(r"^\d{4}-\d{2}-\d{2}$", hire_date):
        return jsonify(error="hire date must be YYYY-MM-DD"), 400
    conn = db()
    conn.execute("UPDATE staff SET hire_date = ? WHERE id = ?",
                 (hire_date, staff_id))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.get("/api/admin/staff/<int:staff_id>")
def admin_staff_detail(staff_id):
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    s = conn.execute(
        "SELECT id, name, email, active, headshot, kernels, birthday, hire_date, created_at"
        " FROM staff WHERE id = ?",
        (staff_id,),
    ).fetchone()
    if not s:
        conn.close()
        return jsonify(error="staff not found"), 404
    credited = conn.execute(
        "SELECT COALESCE(SUM(kernels), 0) AS total, COUNT(*) AS n"
        " FROM kernel_transactions WHERE staff_id = ? AND kernels > 0",
        (staff_id,),
    ).fetchone()
    redeemed = conn.execute(
        "SELECT COALESCE(SUM(-kernels), 0) AS total, COUNT(*) AS n"
        " FROM kernel_transactions WHERE staff_id = ? AND kernels < 0",
        (staff_id,),
    ).fetchone()
    recent = conn.execute(
        "SELECT kt.kernels, kt.reason, kt.order_ref, kt.created_at, u.email AS member_email, u.name AS member_name"
        " FROM kernel_transactions kt LEFT JOIN users u ON u.id = kt.user_id"
        " WHERE kt.staff_id = ? ORDER BY kt.id DESC LIMIT 50",
        (staff_id,),
    ).fetchall()
    staff_rewards = conn.execute(
        "SELECT code, reward_type, created_at FROM loyalty_rewards"
        " WHERE staff_id = ? AND used = 0 ORDER BY created_at DESC",
        (staff_id,),
    ).fetchall()
    staff_gift_cards = conn.execute(
        "SELECT code, amount_cents, balance_cents, created_at FROM gift_cards"
        " WHERE stripe_session_id = ? AND active = 1 AND balance_cents > 0"
        " ORDER BY created_at DESC",
        (f"staff:{staff_id}",),
    ).fetchall()
    conn.close()
    return jsonify(
        id=s["id"], name=s["name"], email=s["email"],
        active=bool(s["active"]), created_at=s["created_at"],
        headshot=s["headshot"] or "", staff_kernels=s["kernels"] or 0,
        birthday=s["birthday"] or "", hire_date=s["hire_date"] or "",
        kernels_credited=credited["total"] or 0, credit_count=credited["n"] or 0,
        kernels_redeemed=redeemed["total"] or 0, redeem_count=redeemed["n"] or 0,
        available_rewards=[
            {"code": rw["code"],
             "label": STAFF_REWARD_TIERS.get(rw["reward_type"], {}).get("label", rw["reward_type"]),
             "created_at": rw["created_at"]}
            for rw in staff_rewards
        ],
        available_gift_cards=[
            {"code": g["code"], "amount_cents": g["amount_cents"],
             "balance_cents": g["balance_cents"], "created_at": g["created_at"]}
            for g in staff_gift_cards
        ],
        recent_activity=[
            {"kernels": r["kernels"], "reason": r["reason"], "note": r["order_ref"] or "",
             "member_email": r["member_email"] or "", "member_name": r["member_name"] or "",
             "created_at": r["created_at"]}
            for r in recent
        ],
    )

# ---------------------------------------------------------------- flavor reviews

@app.get("/api/reviews")
def list_reviews():
    flavor = (request.args.get("flavor") or "").strip().lower()
    if not flavor:
        return jsonify(error="flavor is required"), 400
    conn = db()
    rows = conn.execute(
        "SELECT user_name, rating, text, created_at FROM reviews"
        " WHERE flavor_slug = ? AND approved = 1 ORDER BY created_at DESC",
        (flavor,),
    ).fetchall()
    conn.close()
    reviews = [
        {"name": r["user_name"], "rating": r["rating"], "text": r["text"],
         "created_at": r["created_at"]}
        for r in rows
    ]
    avg = round(sum(r["rating"] for r in reviews) / len(reviews), 1) if reviews else 0
    return jsonify(reviews=reviews, count=len(reviews), average=avg)

@app.post("/api/reviews")
def post_review():
    err = _require_auth_ready()
    if err:
        return err
    user = _current_member()
    if not user:
        return jsonify(error="please log in to leave a review"), 401
    data = request.get_json(force=True) or {}
    flavor = (data.get("flavor") or "").strip().lower()
    try:
        rating = int(data.get("rating", 0))
    except (TypeError, ValueError):
        return jsonify(error="rating is required"), 400
    text = (data.get("text") or "").strip()
    if not flavor:
        return jsonify(error="flavor is required"), 400
    if rating < 1 or rating > 5:
        return jsonify(error="rating must be between 1 and 5 stars"), 400
    if len(text) < 2:
        return jsonify(error="please write a few words"), 400
    if len(text) > 1000:
        return jsonify(error="review is too long (1000 characters max)"), 400
    now = datetime.now(timezone.utc).isoformat()
    conn = db()
    conn.execute(
        """INSERT INTO reviews (flavor_slug, user_id, user_name, rating, text, approved, created_at)
           VALUES (?, ?, ?, ?, ?, 0, ?)
           ON CONFLICT(flavor_slug, user_id) DO UPDATE SET
             rating = excluded.rating, text = excluded.text,
             approved = 0, created_at = excluded.created_at""",
        (flavor, user["id"], user["name"], rating, text, now),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True, pending=True,
                   message="Thanks! Your review will appear once it's approved.")

@app.get("/api/reviews/pending")
def pending_reviews():
    err = _require_auth_ready()
    if err:
        return err
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="not authorized"), 403
    conn = db()
    rows = conn.execute(
        "SELECT id, flavor_slug, user_name, rating, text, created_at FROM reviews"
        " WHERE approved = 0 ORDER BY created_at DESC"
    ).fetchall()
    conn.close()
    return jsonify(reviews=[
        {"id": r["id"], "flavor": r["flavor_slug"], "name": r["user_name"],
         "rating": r["rating"], "text": r["text"], "created_at": r["created_at"]}
        for r in rows
    ])

@app.post("/api/reviews/<int:review_id>/approve")
def approve_review(review_id):
    err = _require_auth_ready()
    if err:
        return err
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="not authorized"), 403
    conn = db()
    conn.execute("UPDATE reviews SET approved = 1 WHERE id = ?", (review_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/reviews/<int:review_id>/reject")
def reject_review(review_id):
    err = _require_auth_ready()
    if err:
        return err
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="not authorized"), 403
    conn = db()
    conn.execute("DELETE FROM reviews WHERE id = ?", (review_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)


# ---------------------------------------------------------------- fundraising + subscriptions

import calendar
import json

CRON_SECRET = os.environ.get("CRON_SECRET", "")

# Fundraising flavors ($8.00/bag = 800 cents) — supporter purchases are
# validated against these 25.
FLAVORS = [
    "Alien Mix", "Bacon", "Banana Pudding", "Birthday Cake", "Buffalo Ranch",
    "Caramel", "Cheddar", "Cheddar Jalapeño", "Cheeseburger", "Churro",
    "Cinnamon Roll", "Cookie and Cream", "Dill Pickle", "Garlic Butter",
    "Garlic Parmesan", "Kettle Corn", "Lemonade", "Muddy Buddy", "Pizza",
    "Salt and Vinegar", "Snickerdoodle", "Strawberry Cheesecake",
    "Sugar Cookie", "White Cheddar", "Nashville Hot",
]
_FLAVOR_LOOKUP = {f.lower(): f for f in FLAVORS}
BAG_PRICE_CENTS = 800

SUB_FREQUENCIES = {
    "biweekly": {"days": 14, "discount": 20, "label": "Every 2 weeks"},
    "monthly": {"days": 30, "discount": 15, "label": "Every month"},
    "bimonthly": {"days": 60, "discount": 10, "label": "Every 2 months"},
}

# ---------------- fundraising helpers ----------------

def _gen_fundraiser_code(conn):
    """Unique 6-char fundraiser code (A-Z0-9)."""
    alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    for _ in range(20):
        code = "".join(secrets.choice(alphabet) for _ in range(6))
        if not conn.execute(
            "SELECT 1 FROM fundraisers WHERE code = ?", (code,)
        ).fetchone():
            return code
    raise RuntimeError("could not generate a unique fundraiser code")

def _gen_seller_referral_code(conn):
    for _ in range(20):
        code = "".join(secrets.choice(CODE_ALPHABET) for _ in range(8))
        if not conn.execute(
            "SELECT 1 FROM fundraiser_sellers WHERE referral_code = ?", (code,)
        ).fetchone():
            return code
    raise RuntimeError("could not generate a unique seller referral code")

def _fundraiser_raised_cents(conn, fundraiser_id):
    """Raised total = SUM(org_share over paid+in_person orders) + sponsor matched."""
    row = conn.execute(
        "SELECT COALESCE(SUM(CAST(subtotal_cents / 2 AS INTEGER)"
        " + donation_cents + roundup_cents), 0) AS orders,"
        " (SELECT COALESCE(SUM(matched_cents), 0) FROM fundraiser_sponsors"
        " WHERE fundraiser_id = ?) AS matched"
        " FROM fundraiser_orders"
        " WHERE fundraiser_id = ? AND status IN ('paid', 'in_person')",
        (fundraiser_id, fundraiser_id),
    ).fetchone()
    return int(row["orders"] or 0) + int(row["matched"] or 0)

def _seller_raised_cents(conn, seller_id):
    row = conn.execute(
        "SELECT COALESCE(SUM(CAST(subtotal_cents / 2 AS INTEGER)"
        " + donation_cents + roundup_cents), 0) AS s"
        " FROM fundraiser_orders"
        " WHERE seller_id = ? AND status IN ('paid', 'in_person')",
        (seller_id,),
    ).fetchone()
    return int(row["s"] or 0)

def _team_raised_cents(conn, fundraiser_id, team_id):
    row = conn.execute(
        "SELECT COALESCE(SUM(CAST(o.subtotal_cents / 2 AS INTEGER)"
        " + o.donation_cents + o.roundup_cents), 0) AS s"
        " FROM fundraiser_orders o JOIN fundraiser_sellers s ON s.id = o.seller_id"
        " WHERE o.fundraiser_id = ? AND s.team_id = ?"
        " AND o.status IN ('paid', 'in_person')",
        (fundraiser_id, team_id),
    ).fetchone()
    return int(row["s"] or 0)

def _days_left(end_date):
    try:
        delta = (datetime.strptime(end_date, "%Y-%m-%d").date()
                 - datetime.now(timezone.utc).date()).days
    except (TypeError, ValueError):
        return 0
    return max(delta, 0)

def _fundraiser_dict(row, raised):
    return {
        "id": row["id"], "code": row["code"], "org_name": row["org_name"],
        "contact_name": row["contact_name"], "contact_email": row["contact_email"],
        "goal_cents": row["goal_cents"], "start_date": row["start_date"],
        "end_date": row["end_date"], "event_days": row["event_days"],
        "status": row["status"], "raised_cents": raised,
        "days_left": _days_left(row["end_date"]),
    }

def _validate_fundraiser_items(raw):
    """Validate [{flavor, quantity}]; qty 1..50 per line. Returns (items, err)."""
    if not isinstance(raw, list) or not raw:
        return None, (jsonify(error="add at least one bag"), 400)
    items = []
    for it in raw:
        if not isinstance(it, dict):
            return None, (jsonify(error="invalid items"), 400)
        flavor = _FLAVOR_LOOKUP.get(((it.get("flavor") or "").strip()).lower())
        try:
            qty = int(it.get("quantity", 0))
        except (TypeError, ValueError):
            return None, (jsonify(error="invalid items"), 400)
        if not flavor:
            return None, (jsonify(error="unknown flavor"), 400)
        if qty < 1 or qty > 50:
            return None, (jsonify(error="quantity must be between 1 and 50 per flavor"), 400)
        items.append({"flavor": flavor, "quantity": qty})
    return items, None

def _items_summary_str(items):
    return ", ".join(
        f"{it['quantity']}x {it['flavor']}" for it in items
        if isinstance(it, dict) and it.get("flavor")
    )

def _next_fundraiser_order_number(conn):
    """Friendly order number FR-1001, FR-1002, ... (retries on collision)."""
    for _ in range(5):
        count = conn.execute(
            "SELECT COUNT(*) AS c FROM fundraiser_orders").fetchone()["c"]
        candidate = f"FR-{1001 + count}"
        if not conn.execute(
            "SELECT 1 FROM fundraiser_orders WHERE order_number = ?",
            (candidate,),
        ).fetchone():
            return candidate
    raise RuntimeError("could not assign a fundraiser order number")

def _clamp_event_days(start_date, event_days):
    """Clamp event_days to 1..31, then to the days remaining in the start month."""
    event_days = max(1, min(31, event_days))
    days_in_month = calendar.monthrange(start_date.year, start_date.month)[1]
    days_remaining = days_in_month - start_date.day + 1
    return max(1, min(event_days, days_remaining))

# ---------------- fundraising endpoints ----------------

@app.post("/api/fundraisers")
def create_fundraiser():
    """Create a fundraiser (public)."""
    data = request.get_json(force=True) or {}
    org_name = (data.get("org_name") or "").strip()[:200]
    contact_name = (data.get("contact_name") or "").strip()[:120]
    contact_email = (data.get("contact_email") or "").strip().lower()[:160]
    try:
        goal_cents = int(data.get("goal_cents") or 0)
    except (TypeError, ValueError):
        return jsonify(error="goal_cents must be an integer number of cents"), 400
    try:
        event_days = int(data.get("event_days") or 0)
    except (TypeError, ValueError):
        return jsonify(error="event_days must be a number of days"), 400
    start_str = (data.get("start_date") or "").strip()
    if not org_name:
        return jsonify(error="organization name is required"), 400
    if not contact_name:
        return jsonify(error="contact name is required"), 400
    if not EMAIL_RE.match(contact_email):
        return jsonify(error="a valid contact email is required"), 400
    if goal_cents <= 0 or goal_cents > 100000000:
        return jsonify(error="goal must be a positive amount"), 400
    try:
        start_date = datetime.strptime(start_str, "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return jsonify(error="start_date must be YYYY-MM-DD"), 400
    event_days = _clamp_event_days(start_date, event_days)
    end_date = start_date + timedelta(days=event_days - 1)

    raw_teams = data.get("teams") or []
    if not isinstance(raw_teams, list):
        return jsonify(error="teams must be a list of names"), 400
    teams = []
    for t in raw_teams[:50]:
        name = (t or "").strip()[:120] if isinstance(t, str) else ""
        if name:
            teams.append(name)
    stretch = []
    for sg in (data.get("stretch_goals") or [])[:50]:
        if not isinstance(sg, dict):
            continue
        try:
            thr = int(sg.get("threshold_cents") or 0)
        except (TypeError, ValueError):
            continue
        label = (sg.get("label") or "").strip()[:200]
        if thr > 0 and label:
            stretch.append({"threshold_cents": thr, "label": label})
    sponsors = []
    for sp in (data.get("sponsors") or [])[:50]:
        if not isinstance(sp, dict):
            continue
        try:
            cap = int(sp.get("match_cap_cents") or 0)
        except (TypeError, ValueError):
            continue
        biz = (sp.get("business_name") or "").strip()[:200]
        if biz and cap > 0:
            sponsors.append({"business_name": biz, "match_cap_cents": cap})

    conn = db()
    code = _gen_fundraiser_code(conn)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        """INSERT INTO fundraisers
           (code, org_name, contact_name, contact_email, goal_cents,
            start_date, end_date, event_days, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'active', ?)""",
        (code, org_name, contact_name, contact_email, goal_cents,
         start_date.isoformat(), end_date.isoformat(), event_days, now),
    )
    fid = cur.lastrowid
    for name in teams:
        conn.execute(
            "INSERT INTO fundraiser_teams (fundraiser_id, name) VALUES (?, ?)",
            (fid, name))
    for sg in stretch:
        conn.execute(
            "INSERT INTO fundraiser_stretch_goals (fundraiser_id, threshold_cents, label)"
            " VALUES (?, ?, ?)",
            (fid, sg["threshold_cents"], sg["label"]))
    for sp in sponsors:
        conn.execute(
            "INSERT INTO fundraiser_sponsors (fundraiser_id, business_name, match_cap_cents)"
            " VALUES (?, ?, ?)",
            (fid, sp["business_name"], sp["match_cap_cents"]))
    conn.commit()
    conn.close()
    return jsonify(id=fid, code=code, org_name=org_name, goal_cents=goal_cents,
                   start_date=start_date.isoformat(),
                   end_date=end_date.isoformat(),
                   event_days=event_days, status="active")

@app.get("/api/fundraisers/by-code/<code>")
def fundraiser_by_code(code):
    """Public fundraiser page data."""
    code = (code or "").strip().upper()
    conn = db()
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE code = ?", (code,)).fetchone()
    if not fr:
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    raised = _fundraiser_raised_cents(conn, fr["id"])
    teams = conn.execute(
        "SELECT id, name FROM fundraiser_teams WHERE fundraiser_id = ? ORDER BY id",
        (fr["id"],)).fetchall()
    team_list = [
        {"id": t["id"], "name": t["name"],
         "raised_cents": _team_raised_cents(conn, fr["id"], t["id"])}
        for t in teams
    ]
    sellers = conn.execute(
        "SELECT id, name, referral_code, team_id, personal_goal_cents, video_url"
        " FROM fundraiser_sellers WHERE fundraiser_id = ? ORDER BY name",
        (fr["id"],)).fetchall()
    seller_list = [
        {"id": s["id"], "name": s["name"], "referral_code": s["referral_code"],
         "team_id": s["team_id"] or 0,
         "raised_cents": _seller_raised_cents(conn, s["id"]),
         "personal_goal_cents": s["personal_goal_cents"] or 0,
         "video_url": s["video_url"] or ""}
        for s in sellers
    ]
    goals = conn.execute(
        "SELECT threshold_cents, label FROM fundraiser_stretch_goals"
        " WHERE fundraiser_id = ? ORDER BY threshold_cents",
        (fr["id"],)).fetchall()
    goal_list = [
        {"threshold_cents": g["threshold_cents"], "label": g["label"],
         "unlocked": raised >= (g["threshold_cents"] or 0)}
        for g in goals
    ]
    sponsors = conn.execute(
        "SELECT business_name, match_cap_cents, matched_cents FROM fundraiser_sponsors"
        " WHERE fundraiser_id = ? ORDER BY id",
        (fr["id"],)).fetchall()
    sponsor_list = [
        {"business_name": sp["business_name"],
         "match_cap_cents": sp["match_cap_cents"],
         "matched_cents": sp["matched_cents"]}
        for sp in sponsors
    ]
    ticker = conn.execute(
        "SELECT message, created_at FROM fundraiser_ticker"
        " WHERE fundraiser_id = ? ORDER BY id DESC LIMIT 10",
        (fr["id"],)).fetchall()
    ticker_list = [
        {"message": t["message"], "created_at": t["created_at"]} for t in ticker
    ]
    conn.close()
    return jsonify(fundraiser=_fundraiser_dict(fr, raised), teams=team_list,
                   sellers=seller_list, stretch_goals=goal_list,
                   sponsors=sponsor_list, ticker=ticker_list)

@app.post("/api/fundraisers/<int:fid>/sellers")
def add_fundraiser_seller(fid):
    """Add a seller to a fundraiser (public; organizer flow)."""
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()[:120]
    email = (data.get("email") or "").strip().lower()[:160]
    try:
        team_id = int(data.get("team_id") or 0)
    except (TypeError, ValueError):
        return jsonify(error="invalid team"), 400
    if not name:
        return jsonify(error="seller name is required"), 400
    if email and not EMAIL_RE.match(email):
        return jsonify(error="invalid email address"), 400
    conn = db()
    if not conn.execute(
        "SELECT 1 FROM fundraisers WHERE id = ?", (fid,)
    ).fetchone():
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    if team_id:
        t = conn.execute(
            "SELECT 1 FROM fundraiser_teams WHERE id = ? AND fundraiser_id = ?",
            (team_id, fid)).fetchone()
        if not t:
            conn.close()
            return jsonify(error="team not found"), 404
    ref = _gen_seller_referral_code(conn)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        """INSERT INTO fundraiser_sellers
           (fundraiser_id, team_id, name, email, referral_code, created_at)
           VALUES (?, ?, ?, ?, ?, ?)""",
        (fid, team_id, name, email, ref, now))
    sid = cur.lastrowid
    conn.commit()
    conn.close()
    return jsonify(id=sid, name=name, referral_code=ref,
                   store_url=f"{SITE_URL}/#seller-store?code={ref}")

@app.patch("/api/fundraisers/sellers/<int:seller_id>")
def update_fundraiser_seller(seller_id):
    """Seller tools (public)."""
    data = request.get_json(force=True) or {}
    updates = {}
    if "name" in data:
        name = (data.get("name") or "").strip()[:120]
        if not name:
            return jsonify(error="name cannot be blank"), 400
        updates["name"] = name
    if "video_url" in data:
        updates["video_url"] = (data.get("video_url") or "").strip()[:500]
    if "personal_goal_cents" in data:
        try:
            pg = int(data.get("personal_goal_cents") or 0)
        except (TypeError, ValueError):
            return jsonify(error="personal_goal_cents must be an integer"), 400
        if pg < 0:
            return jsonify(error="personal_goal_cents cannot be negative"), 400
        updates["personal_goal_cents"] = pg
    if not updates:
        return jsonify(error="nothing to update"), 400
    conn = db()
    seller = conn.execute(
        "SELECT * FROM fundraiser_sellers WHERE id = ?", (seller_id,)
    ).fetchone()
    if not seller:
        conn.close()
        return jsonify(error="seller not found"), 404
    # Require the seller's own referral code (their secret) to modify.
    if (data.get("referral_code") or "").strip().upper() != (seller["referral_code"] or "").upper():
        conn.close()
        return jsonify(error="not authorized"), 403
    clause = ", ".join(f"{k} = ?" for k in updates)
    conn.execute(f"UPDATE fundraiser_sellers SET {clause} WHERE id = ?",
                 (*updates.values(), seller_id))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.get("/api/fundraisers/store/<referral_code>")
def fundraiser_store(referral_code):
    """Seller store page data (public)."""
    ref = (referral_code or "").strip().upper()
    conn = db()
    s = conn.execute(
        "SELECT * FROM fundraiser_sellers WHERE referral_code = ?", (ref,)).fetchone()
    if not s:
        conn.close()
        return jsonify(error="seller not found"), 404
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE id = ?", (s["fundraiser_id"],)).fetchone()
    seller_raised = _seller_raised_cents(conn, s["id"])
    fr_out = None
    if fr:
        fr_out = {"org_name": fr["org_name"], "code": fr["code"],
                  "raised_cents": _fundraiser_raised_cents(conn, fr["id"]),
                  "goal_cents": fr["goal_cents"],
                  "end_date": fr["end_date"],
                  "days_left": _days_left(fr["end_date"])}
    conn.close()
    return jsonify(
        seller={"name": s["name"], "referral_code": s["referral_code"],
                "video_url": s["video_url"] or "",
                "personal_goal_cents": s["personal_goal_cents"] or 0,
                "raised_cents": seller_raised},
        fundraiser=fr_out)

@app.post("/api/fundraisers/checkout")
def fundraiser_checkout():
    """Supporter purchase (public). Creates a Stripe PaymentIntent."""
    data = request.get_json(force=True) or {}
    fcode = (data.get("fundraiser_code") or "").strip().upper()
    scode = (data.get("seller_referral_code") or "").strip().upper()
    customer_name = (data.get("customer_name") or "").strip()[:120]
    customer_email = (data.get("customer_email") or "").strip().lower()[:160]
    ship_name = (data.get("ship_name") or "").strip()[:120]
    ship_street = (data.get("ship_street") or "").strip()[:200]
    ship_city = (data.get("ship_city") or "").strip()[:120]
    ship_state = (data.get("ship_state") or "").strip().upper()[:2]
    ship_zip = (data.get("ship_zip") or "").strip()[:10]

    conn = db()
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE code = ?", (fcode,)).fetchone()
    if not fr:
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    if fr["status"] != "active":
        conn.close()
        return jsonify(error="this fundraiser has ended"), 400
    seller_id = 0
    if scode:
        s = conn.execute(
            "SELECT id FROM fundraiser_sellers"
            " WHERE referral_code = ? AND fundraiser_id = ?",
            (scode, fr["id"])).fetchone()
        if not s:
            conn.close()
            return jsonify(error="seller not found"), 404
        seller_id = s["id"]
    conn.close()

    items, err = _validate_fundraiser_items(data.get("items"))
    if err:
        return err[0], err[1]
    total_qty = sum(it["quantity"] for it in items)
    subtotal = BAG_PRICE_CENTS * total_qty

    if not customer_name:
        return jsonify(error="your name is required"), 400
    if not EMAIL_RE.match(customer_email):
        return jsonify(error="a valid email is required"), 400
    if not ship_name or not ship_street or not ship_city or not ship_state or not ship_zip:
        return jsonify(error="a complete shipping address is required"), 400

    try:
        donation = int(data.get("donation_cents") or 0)
    except (TypeError, ValueError):
        return jsonify(error="donation_cents must be an integer"), 400
    if donation < 0 or donation > 100000:
        return jsonify(error="donation must be between $0 and $1,000"), 400
    roundup = 0
    if data.get("round_up") and subtotal % 100:
        roundup = (subtotal // 100 + 1) * 100 - subtotal

    ship_cents = _cheapest_shipping_cents(ship_zip, total_qty)
    ship_note = ""
    if ship_cents is None:
        ship_cents = 0
        ship_note = "shipping unavailable — we'll confirm shipping by email"
    total = subtotal + donation + roundup + ship_cents
    if total < 50:
        return jsonify(error="order total is too small"), 400

    try:
        pi = stripe.PaymentIntent.create(
            amount=total,
            currency="usd",
            metadata={
                "type": "fundraiser_order",
                "fundraiser_code": fcode,
                "seller_code": scode,
                "seller_id": str(seller_id),
                "customer_name": customer_name,
                "customer_email": customer_email,
                "ship_name": ship_name,
                "ship_street": ship_street,
                "ship_city": ship_city,
                "ship_state": ship_state,
                "ship_zip": ship_zip,
                "items": json.dumps(items)[:450],
                "subtotal_cents": str(subtotal),
                "donation_cents": str(donation),
                "roundup_cents": str(roundup),
                "shipping_cents": str(ship_cents),
                "total_cents": str(total),
            },
        )
    except stripe.error.StripeError:
        return jsonify(error="the payment service could not start checkout"), 502
    out = {
        "client_secret": pi.client_secret,
        "payment_intent_id": pi.id,
        "breakdown": {
            "subtotal_cents": subtotal, "donation_cents": donation,
            "roundup_cents": roundup, "shipping_cents": ship_cents,
            "total_cents": total,
        },
    }
    if ship_note:
        out["shipping_note"] = ship_note
    return jsonify(out)

@app.post("/api/fundraisers/orders/confirm")
def fundraiser_order_confirm():
    """Record a fundraiser order after Stripe confirms (public)."""
    data = request.get_json(force=True) or {}
    pi_id = (data.get("payment_intent_id") or "").strip()
    if not pi_id:
        return jsonify(error="payment_intent_id is required"), 400
    try:
        pi = stripe.PaymentIntent.retrieve(pi_id)
    except stripe.error.StripeError:
        return jsonify(error="could not verify the payment"), 502
    if pi.get("status") != "succeeded":
        return jsonify(error="payment has not completed yet"), 402
    meta = pi.get("metadata") or {}
    if meta.get("type") != "fundraiser_order":
        return jsonify(error="not a fundraiser payment"), 400

    conn = db()
    existing = conn.execute(
        "SELECT order_number FROM fundraiser_orders WHERE stripe_payment_intent_id = ?",
        (pi_id,)).fetchone()
    if existing:
        conn.close()
        return jsonify(ok=True, order_number=existing["order_number"], already=True)

    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE code = ?",
        (meta.get("fundraiser_code") or "",)).fetchone()
    if not fr:
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    try:
        seller_id = int(meta.get("seller_id") or 0)
    except (TypeError, ValueError):
        seller_id = 0
    try:
        items = json.loads(meta.get("items") or "[]")
    except (TypeError, ValueError):
        items = []
    total_qty = sum(int(it.get("quantity", 0)) for it in items
                    if isinstance(it, dict))

    def _mi(key):
        try:
            return int(meta.get(key) or 0)
        except (TypeError, ValueError):
            return 0

    subtotal = _mi("subtotal_cents") or BAG_PRICE_CENTS * total_qty
    donation = _mi("donation_cents")
    roundup = _mi("roundup_cents")
    ship_cents = _mi("shipping_cents")
    total = _mi("total_cents") or (subtotal + donation + roundup + ship_cents)
    customer_name = (meta.get("customer_name") or "")[:120]
    customer_email = (meta.get("customer_email") or "")[:160]
    now = datetime.now(timezone.utc).isoformat()

    try:
        order_number = _next_fundraiser_order_number(conn)
        # Shippo label (never blocks the order — blank fields = admin retry).
        label_url, tracking_number = _create_shippo_label(
            _shippo_address_to(
                name=(meta.get("ship_name") or "")[:120] or customer_name,
                street1=(meta.get("ship_street") or "")[:200],
                city=(meta.get("ship_city") or "")[:120],
                state=(meta.get("ship_state") or "")[:2],
                zip_code=(meta.get("ship_zip") or "")[:10],
            ),
            total_qty,
            order_ref=order_number,
        )
        label_created_at = now if label_url else ""
        conn.execute(
            """INSERT INTO fundraiser_orders
               (fundraiser_id, seller_id, order_number, customer_name, customer_email,
                ship_name, ship_street, ship_city, ship_state, ship_zip,
                items, subtotal_cents, donation_cents, roundup_cents,
                shipping_cents, total_cents, stripe_payment_intent_id, status,
                shippo_label_url, shippo_tracking_number, shippo_label_created_at,
                created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'paid', ?, ?, ?, ?)""",
            (fr["id"], seller_id, order_number, customer_name, customer_email,
             (meta.get("ship_name") or "")[:120], (meta.get("ship_street") or "")[:200],
             (meta.get("ship_city") or "")[:120], (meta.get("ship_state") or "")[:2],
             (meta.get("ship_zip") or "")[:10],
             json.dumps(items), subtotal, donation, roundup, ship_cents, total,
             pi_id, label_url or "", tracking_number or "", label_created_at, now),
        )
    except RuntimeError:
        conn.close()
        return jsonify(error="could not record the order"), 500

    # Ticker entry.
    first = customer_name.split()[0] if customer_name else "A supporter"
    bag_word = "bag" if total_qty == 1 else "bags"
    conn.execute(
        "INSERT INTO fundraiser_ticker (fundraiser_id, message, created_at)"
        " VALUES (?, ?, ?)",
        (fr["id"], f"{first} just bought {total_qty} {bag_word}", now))

    # Sponsor matching: the donation+roundup portion is matched up to each
    # sponsor's cap, oldest sponsor first.
    matchable = donation + roundup
    if matchable > 0:
        sponsors = conn.execute(
            "SELECT id, match_cap_cents, matched_cents FROM fundraiser_sponsors"
            " WHERE fundraiser_id = ? ORDER BY id", (fr["id"],)).fetchall()
        remaining = matchable
        for sp in sponsors:
            if remaining <= 0:
                break
            room = (sp["match_cap_cents"] or 0) - (sp["matched_cents"] or 0)
            take = min(room, remaining)
            if take > 0:
                conn.execute(
                    "UPDATE fundraiser_sponsors SET matched_cents = matched_cents + ?"
                    " WHERE id = ?", (take, sp["id"]))
                remaining -= take
    conn.commit()
    conn.close()

    summary = _items_summary_str(items)
    dollars = lambda c: f"${c / 100:,.2f}"
    receipt_html = (
        '<html><body style="font-family: Arial, sans-serif; line-height: 1.6;">'
        f"<p>Hi {customer_name or 'there'},</p>"
        f"<p>Thanks for supporting <strong>{fr['org_name']}</strong>!"
        " Your fundraiser order is confirmed. &#x1F37F;</p>"
        f"<p><strong>Order:</strong> {order_number}"
        f"<br><strong>Items:</strong> {summary}"
        f"<br><strong>Donation:</strong> {dollars(donation)}</p>"
        f"<p><strong>Total charged:</strong> {dollars(total)}</p>"
        "<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>"
        "</body></html>"
    )
    try:
        if customer_email:
            send_email(customer_email,
                       f"Thanks for supporting {fr['org_name']}!", receipt_html)
    except Exception:
        pass  # order is already recorded; never fail the response on email
    shipping = ", ".join(
        x for x in [meta.get("ship_name"), meta.get("ship_street"),
                    meta.get("ship_city"), meta.get("ship_state"),
                    meta.get("ship_zip")] if x)
    notify_merchant_of_order(order_number, customer_name, customer_email,
                             summary, total, "", 0, "", shipping,
                             label_url or "", tracking_number or "")
    return jsonify(ok=True, order_number=order_number)

@app.post("/api/fundraisers/in-person-sale")
def fundraiser_in_person_sale():
    """QR scan mode: record a cash/card in-person sale (public)."""
    data = request.get_json(force=True) or {}
    scode = (data.get("seller_referral_code") or "").strip().upper()
    try:
        amount_cents = int(data.get("amount_cents") or 0)
    except (TypeError, ValueError):
        return jsonify(error="amount_cents must be an integer"), 400
    if amount_cents <= 0:
        return jsonify(error="amount_cents must be positive"), 400
    items, err = _validate_fundraiser_items(data.get("items"))
    if err:
        return err[0], err[1]
    conn = db()
    s = conn.execute(
        "SELECT * FROM fundraiser_sellers WHERE referral_code = ?",
        (scode,)).fetchone()
    if not s:
        conn.close()
        return jsonify(error="seller not found"), 404
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE id = ?", (s["fundraiser_id"],)).fetchone()
    if not fr or fr["status"] != "active":
        conn.close()
        return jsonify(error="this fundraiser has ended"), 400
    total_qty = sum(it["quantity"] for it in items)
    subtotal = BAG_PRICE_CENTS * total_qty
    now = datetime.now(timezone.utc).isoformat()
    try:
        order_number = _next_fundraiser_order_number(conn)
        conn.execute(
            """INSERT INTO fundraiser_orders
               (fundraiser_id, seller_id, order_number, customer_name, customer_email,
                items, subtotal_cents, total_cents, status, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'in_person', ?)""",
            (fr["id"], s["id"], order_number, s["name"], s["email"] or "",
             json.dumps(items), subtotal, amount_cents, now),
        )
    except RuntimeError:
        conn.close()
        return jsonify(error="could not record the sale"), 500
    bag_word = "bag" if total_qty == 1 else "bags"
    conn.execute(
        "INSERT INTO fundraiser_ticker (fundraiser_id, message, created_at)"
        " VALUES (?, ?, ?)",
        (fr["id"], f"{s['name']} logged an in-person sale of {total_qty} {bag_word}",
         now))
    conn.commit()
    conn.close()
    return jsonify(ok=True, order_number=order_number)

@app.get("/api/fundraisers/<int:fid>/dashboard")
def fundraiser_dashboard(fid):
    """Organizer view — requires the secret fundraiser code."""
    code = (request.args.get("code") or "").strip().upper()
    conn = db()
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE id = ? AND code = ?", (fid, code)).fetchone()
    if not fr:
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    raised = _fundraiser_raised_cents(conn, fid)
    sellers = conn.execute(
        "SELECT id, name, email, referral_code, team_id, shared, nudged"
        " FROM fundraiser_sellers WHERE fundraiser_id = ? ORDER BY name",
        (fid,)).fetchall()
    seller_list = [
        {"id": s["id"], "name": s["name"], "email": s["email"],
         "referral_code": s["referral_code"], "shared": bool(s["shared"]),
         "nudged": bool(s["nudged"]),
         "raised_cents": _seller_raised_cents(conn, s["id"]),
         "team_id": s["team_id"] or 0}
        for s in sellers
    ]
    teams = conn.execute(
        "SELECT id, name FROM fundraiser_teams WHERE fundraiser_id = ? ORDER BY id",
        (fid,)).fetchall()
    team_list = [{"id": t["id"], "name": t["name"]} for t in teams]
    orders = conn.execute(
        "SELECT fo.order_number, fo.customer_name, fo.items, fo.total_cents,"
        " fo.status, fo.created_at, s.name AS seller_name"
        " FROM fundraiser_orders fo"
        " LEFT JOIN fundraiser_sellers s ON s.id = fo.seller_id"
        " WHERE fo.fundraiser_id = ? ORDER BY fo.id DESC LIMIT 20",
        (fid,)).fetchall()
    order_list = [
        {"order_number": o["order_number"], "customer_name": o["customer_name"],
         "items": o["items"], "total_cents": o["total_cents"],
         "status": o["status"], "seller_name": o["seller_name"] or "",
         "created_at": o["created_at"]}
        for o in orders
    ]
    order_count = conn.execute(
        "SELECT COUNT(*) AS c FROM fundraiser_orders WHERE fundraiser_id = ?",
        (fid,)).fetchone()["c"]
    conn.close()
    return jsonify(fundraiser=_fundraiser_dict(fr, raised), sellers=seller_list,
                   teams=team_list, orders=order_list,
                   totals={"raised_cents": raised, "order_count": order_count})

def _verify_fundraiser_code(conn, fid, code):
    """Return the fundraiser row if the secret code matches, else None."""
    code = (code or "").strip().upper()
    if not code:
        return None
    return conn.execute(
        "SELECT * FROM fundraisers WHERE id = ? AND code = ?", (fid, code)
    ).fetchone()

@app.post("/api/fundraisers/<int:fid>/nudge")
def fundraiser_nudge(fid):
    data = request.get_json(force=True) or {}
    try:
        seller_id = int(data.get("seller_id") or 0)
    except (TypeError, ValueError):
        return jsonify(error="seller_id is required"), 400
    conn = db()
    if not _verify_fundraiser_code(conn, fid, data.get("code")):
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    if not conn.execute(
        "SELECT 1 FROM fundraiser_sellers WHERE id = ? AND fundraiser_id = ?",
        (seller_id, fid),
    ).fetchone():
        conn.close()
        return jsonify(error="seller not found"), 404
    conn.execute(
        "UPDATE fundraiser_sellers SET nudged = 1 WHERE id = ?", (seller_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/fundraisers/<int:fid>/relaunch")
def fundraiser_relaunch(fid):
    """Clone a fundraiser: fresh code/dates, same teams/sellers/goals/sponsors."""
    data = request.get_json(force=True) or {}
    conn = db()
    fr = _verify_fundraiser_code(conn, fid, data.get("code"))
    if not fr:
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    today = datetime.now(timezone.utc).date()
    event_days = _clamp_event_days(today, fr["event_days"] or 1)
    end_date = today + timedelta(days=event_days - 1)
    code = _gen_fundraiser_code(conn)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        """INSERT INTO fundraisers
           (code, org_name, contact_name, contact_email, goal_cents,
            start_date, end_date, event_days, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'active', ?)""",
        (code, fr["org_name"], fr["contact_name"], fr["contact_email"],
         fr["goal_cents"], today.isoformat(), end_date.isoformat(),
         event_days, now))
    new_id = cur.lastrowid
    team_map = {}
    for t in conn.execute(
        "SELECT id, name FROM fundraiser_teams WHERE fundraiser_id = ?",
        (fid,)).fetchall():
        tc = conn.execute(
            "INSERT INTO fundraiser_teams (fundraiser_id, name) VALUES (?, ?)",
            (new_id, t["name"]))
        team_map[t["id"]] = tc.lastrowid
    for s in conn.execute(
        "SELECT * FROM fundraiser_sellers WHERE fundraiser_id = ?",
        (fid,)).fetchall():
        ref = _gen_seller_referral_code(conn)
        conn.execute(
            """INSERT INTO fundraiser_sellers
               (fundraiser_id, team_id, name, email, referral_code, video_url,
                personal_goal_cents, shared, nudged, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, 0, 0, ?)""",
            (new_id, team_map.get(s["team_id"], 0), s["name"], s["email"],
             ref, s["video_url"], s["personal_goal_cents"], now))
    for sg in conn.execute(
        "SELECT threshold_cents, label FROM fundraiser_stretch_goals"
        " WHERE fundraiser_id = ?", (fid,)).fetchall():
        conn.execute(
            "INSERT INTO fundraiser_stretch_goals (fundraiser_id, threshold_cents, label)"
            " VALUES (?, ?, ?)",
            (new_id, sg["threshold_cents"], sg["label"]))
    for sp in conn.execute(
        "SELECT business_name, match_cap_cents FROM fundraiser_sponsors"
        " WHERE fundraiser_id = ?", (fid,)).fetchall():
        conn.execute(
            "INSERT INTO fundraiser_sponsors"
            " (fundraiser_id, business_name, match_cap_cents, matched_cents)"
            " VALUES (?, ?, ?, 0)",
            (new_id, sp["business_name"], sp["match_cap_cents"]))
    conn.commit()
    conn.close()
    return jsonify(id=new_id, code=code)

@app.post("/api/fundraisers/<int:fid>/complete")
def fundraiser_complete(fid):
    data = request.get_json(force=True) or {}
    conn = db()
    if not _verify_fundraiser_code(conn, fid, data.get("code")):
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    conn.execute(
        "UPDATE fundraisers SET status = 'completed' WHERE id = ?", (fid,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

# ---------------- subscription helpers ----------------

def _validate_subscription_items(raw):
    """Validate [{flavor, quantity}]; 1..12 total bags. Returns (items, err)."""
    if not isinstance(raw, list) or not raw:
        return None, (jsonify(error="choose at least one bag"), 400)
    items = []
    total_qty = 0
    for it in raw:
        if not isinstance(it, dict):
            return None, (jsonify(error="invalid items"), 400)
        flavor = _FLAVOR_LOOKUP.get(((it.get("flavor") or "").strip()).lower())
        try:
            qty = int(it.get("quantity", 0))
        except (TypeError, ValueError):
            return None, (jsonify(error="invalid items"), 400)
        if not flavor:
            return None, (jsonify(error="unknown flavor"), 400)
        if qty < 1 or qty > 12:
            return None, (jsonify(error="quantity must be between 1 and 12 per flavor"), 400)
        items.append({"flavor": flavor, "quantity": qty})
        total_qty += qty
    if total_qty < 1 or total_qty > 12:
        return None, (jsonify(error="subscriptions are 1 to 12 bags per delivery"), 400)
    return items, None

def _per_delivery_cents(items, discount_percent):
    bags = sum(it["quantity"] for it in items if isinstance(it, dict))
    return int(round(BAG_PRICE_CENTS * bags * (1 - discount_percent / 100)))

def _new_confirm_token():
    return secrets.token_urlsafe(24)

def _render_subscription_template(text, ctx):
    out = text or ""
    for key, val in ctx.items():
        out = out.replace("{{" + key + "}}", str(val))
    return out

def _subscription_template(conn):
    row = conn.execute(
        "SELECT subject, body_html FROM subscription_email_templates WHERE name = 'reminder'"
    ).fetchone()
    if row and row["subject"]:
        return row["subject"], row["body_html"]
    return _SUBSCRIPTION_REMINDER_SUBJECT, _SUBSCRIPTION_REMINDER_BODY

def _get_or_create_stripe_customer(conn, user):
    """user is a full users row. Returns the Stripe customer id."""
    cid = user["stripe_customer_id"] if "stripe_customer_id" in user.keys() else ""
    cid = cid or ""
    if cid:
        try:
            cust = stripe.Customer.retrieve(cid)
            if not cust.get("deleted"):
                return cid
        except stripe.error.StripeError:
            pass
    cust = stripe.Customer.create(email=user["email"], name=user["name"] or "")
    conn.execute(
        "UPDATE users SET stripe_customer_id = ? WHERE id = ?",
        (cust.id, user["id"]))
    conn.commit()
    return cust.id

def _stripe_error_message(e):
    # Never expose raw Stripe internals; prefer Stripe's own user-facing text.
    return getattr(e, "user_message", None) or "the payment could not be processed"

def _notify_renewal_failure(conn, sub, renewal, reason):
    """Email customer + merchant when a subscription renewal charge fails."""
    attempts = (renewal["failed_attempts"] or 0) + 1
    # After 3 failed attempts, mark the subscription past_due so it stops retrying silently.
    if attempts >= 3:
        conn.execute(
            "UPDATE subscriptions SET status = 'past_due' WHERE id = ?",
            (sub["id"],))
    cust_email = sub["ship_email"] or ""
    cust_name = (sub["ship_name"] or "there").split()[0]
    subject = "Action needed: your Pop-A-Licious subscription payment failed"
    html = f"""<p>Hi {cust_name},</p>
<p>We tried to charge your Pop-A-Licious subscription renewal but the payment failed ({reason}).</p>
<p>Please update your payment method or confirm your flavors here:<br>
<a href="{SITE_URL}/#my-subscriptions">Manage your subscription</a></p>
<p>We'll try again tomorrow. After 3 failed attempts your subscription will be paused.</p>
<p>— Pop-A-Licious</p>"""
    try:
        if cust_email:
            _send_email(cust_email, subject, html)
        _send_email(ORDER_NOTIFY_EMAIL,
                    f"Subscription renewal FAILED (sub #{sub['id']})",
                    f"<p>Renewal {renewal['id']} for subscription {sub['id']} ({cust_email}) failed: {reason}. Attempt {attempts}.</p>")
    except Exception:
        pass

def _attempt_subscription_charge(conn, sub, renewal, items):
    """Charge one subscription renewal off-session.

    Writes the orders row, marks the renewal, and advances the billing
    cycle — but does NOT commit (the caller commits, so cron can batch).
    Returns (True, payload) on success, (False, (response, 402)) on failure.
    """
    disc = SUB_FREQUENCIES.get(sub["frequency"], {}).get(
        "discount", sub["discount_percent"] or 0)
    per = _per_delivery_cents(items, disc)
    bags = sum(it["quantity"] for it in items if isinstance(it, dict))
    ship = _cheapest_shipping_cents(sub["ship_zip"], bags) if bags else 0
    ship = ship or 0
    amount = per + ship
    if amount < 50:
        return False, (jsonify(error="renewal total is too small to charge"), 402)
    if not sub["stripe_customer_id"] or not sub["stripe_payment_method_id"]:
        return False, (jsonify(error="no payment method on file"), 402)
    bag_word = "bag" if bags == 1 else "bags"
    try:
        pi = stripe.PaymentIntent.create(
            amount=amount,
            currency="usd",
            customer=sub["stripe_customer_id"],
            payment_method=sub["stripe_payment_method_id"],
            off_session=True,
            confirm=True,
            description=f"Pop-A-Licious subscription renewal ({bags} {bag_word})",
            receipt_email=(sub["ship_email"] or None),
        )
    except stripe.error.StripeError as e:
        conn.execute(
            "UPDATE subscription_renewals SET status = 'failed', failed_attempts = failed_attempts + 1 WHERE id = ?",
            (renewal["id"],))
        _notify_renewal_failure(conn, sub, renewal, _stripe_error_message(e))
        return False, (jsonify(error=_stripe_error_message(e)), 402)
    if pi.get("status") not in ("succeeded", "processing"):
        conn.execute(
            "UPDATE subscription_renewals SET status = 'failed', failed_attempts = failed_attempts + 1 WHERE id = ?",
            (renewal["id"],))
        _notify_renewal_failure(conn, sub, renewal, "the payment could not be completed")
        return False, (jsonify(error="the payment could not be completed"), 402)

    now = datetime.now(timezone.utc).isoformat()
    summary = _items_summary_str(items)
    ship_addr = ", ".join(
        x for x in [sub["ship_name"], sub["ship_street"], sub["ship_city"],
                    sub["ship_state"], sub["ship_zip"]] if x)
    # Shippo label (never blocks the charge — blank fields = admin retry).
    label_url, tracking_number = _create_shippo_label(
        _shippo_address_to(
            name=sub["ship_name"] or "",
            street1=sub["ship_street"] or "",
            city=sub["ship_city"] or "",
            state=sub["ship_state"] or "",
            zip_code=sub["ship_zip"] or "",
        ),
        bags,
        order_ref=f"sub_{pi.id}",
    )
    label_created_at = now if label_url else ""
    cur = conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, total_qty,
            shippo_label_url, shippo_tracking_number, shippo_label_created_at,
            created_at)
           VALUES (?, ?, ?, ?, ?, ?, '', 0, '', '', ?, ?, ?, ?, ?)""",
        (f"sub_{pi.id}", sub["ship_email"] or "", sub["ship_name"] or "",
         ship_addr, summary, amount, bags,
         label_url or "", tracking_number or "", label_created_at, now))
    order_id = cur.lastrowid
    # Advance the billing cycle from the later of the old billing date / today.
    days = SUB_FREQUENCIES.get(sub["frequency"], {}).get("days", 30)
    try:
        base = datetime.strptime(
            sub["next_billing_date"], "%Y-%m-%d").date()
    except (TypeError, ValueError):
        base = datetime.now(timezone.utc).date()
    new_next = max(base, datetime.now(timezone.utc).date()) + timedelta(days=days)
    conn.execute(
        "UPDATE subscription_renewals SET status = 'charged', charged_at = ?,"
        " order_id = ?, amount_cents = ? WHERE id = ?",
        (now, order_id, amount, renewal["id"]))
    conn.execute(
        "UPDATE subscriptions SET next_billing_date = ?, last_billed_at = ? WHERE id = ?",
        (new_next.isoformat(), now, sub["id"]))
    conn.execute(
        "INSERT INTO subscription_renewals (subscription_id, billing_date, status, confirm_token)"
        " VALUES (?, ?, 'pending', ?)",
        (sub["id"], new_next.isoformat(), _new_confirm_token()))
    # Loyalty: 1 Kernel per $1 on the subscription total.
    if sub["user_id"]:
        urow = conn.execute(
            "SELECT id FROM users WHERE id = ?", (sub["user_id"],)).fetchone()
        if urow:
            _credit_kernels(conn, urow["id"],
                            amount // 100 * KERNELS_PER_DOLLAR,
                            "subscription", order_ref=f"sub_{pi.id}")
    return True, {
        "order_number": 1000 + order_id,
        "payment_intent_id": pi.id,
        "summary": summary,
        "amount": amount,
        "ship_addr": ship_addr,
        "label_url": label_url or "",
        "tracking_number": tracking_number or "",
    }

# ---------------- subscription endpoints ----------------

@app.post("/api/subscriptions/setup-intent")
def subscription_setup_intent():
    """Create a SetupIntent for saving a card (auth required)."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    conn = db()
    full = conn.execute(
        "SELECT * FROM users WHERE id = ?", (user["id"],)).fetchone()
    try:
        customer_id = _get_or_create_stripe_customer(conn, full)
        si = stripe.SetupIntent.create(customer=customer_id, usage="off_session")
    except stripe.error.StripeError:
        conn.close()
        return jsonify(error="the payment service could not start setup"), 502
    conn.close()
    return jsonify(client_secret=si.client_secret, customer_id=customer_id)

@app.post("/api/subscriptions")
def create_subscription():
    """Create a subscription (auth required)."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    data = request.get_json(force=True) or {}
    payment_method_id = (data.get("payment_method_id") or "").strip()
    frequency = (data.get("frequency") or "").strip()
    ship = data.get("shipping") or {}
    if not isinstance(ship, dict):
        return jsonify(error="invalid shipping"), 400
    ship_name = (ship.get("name") or "").strip()[:120]
    ship_street = (ship.get("street") or "").strip()[:200]
    ship_city = (ship.get("city") or "").strip()[:120]
    ship_state = (ship.get("state") or "").strip().upper()[:2]
    ship_zip = (ship.get("zip") or "").strip()[:10]

    items, err = _validate_subscription_items(data.get("items"))
    if err:
        return err[0], err[1]
    if frequency not in SUB_FREQUENCIES:
        return jsonify(error="frequency must be biweekly, monthly, or bimonthly"), 400
    if not ship_name or not ship_street or not ship_city or not ship_state or not ship_zip:
        return jsonify(error="a complete shipping address is required"), 400
    if not payment_method_id:
        return jsonify(error="payment_method_id is required"), 400

    conn = db()
    full = conn.execute(
        "SELECT * FROM users WHERE id = ?", (user["id"],)).fetchone()
    try:
        customer_id = _get_or_create_stripe_customer(conn, full)
        stripe.PaymentMethod.attach(payment_method_id, customer=customer_id)
        stripe.Customer.modify(
            customer_id,
            invoice_settings={"default_payment_method": payment_method_id})
    except stripe.error.StripeError:
        conn.close()
        return jsonify(error="could not save your payment method"), 502

    freq = SUB_FREQUENCIES[frequency]
    next_billing = (datetime.now(timezone.utc).date()
                    + timedelta(days=freq["days"])).isoformat()
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        """INSERT INTO subscriptions
           (user_id, stripe_customer_id, stripe_payment_method_id, items, frequency,
            discount_percent, status, next_billing_date,
            ship_name, ship_street, ship_city, ship_state, ship_zip, ship_email,
            created_at)
           VALUES (?, ?, ?, ?, ?, ?, 'active', ?, ?, ?, ?, ?, ?, ?, ?)""",
        (user["id"], customer_id, payment_method_id, json.dumps(items), frequency,
         freq["discount"], next_billing,
         ship_name, ship_street, ship_city, ship_state, ship_zip, full["email"],
         now))
    sub_id = cur.lastrowid
    conn.execute(
        "INSERT INTO subscription_renewals (subscription_id, billing_date, status, confirm_token)"
        " VALUES (?, ?, 'pending', ?)",
        (sub_id, next_billing, _new_confirm_token()))
    conn.commit()
    conn.close()
    # Welcome email (never blocks the response if sending fails).
    _send_subscription_welcome_email(
        full["name"] or ship_name, full["email"], items, frequency, next_billing)
    return jsonify(id=sub_id, next_billing_date=next_billing,
                   per_delivery_cents=_per_delivery_cents(items, freq["discount"]),
                   discount_percent=freq["discount"])

@app.get("/api/subscriptions/mine")
def my_subscriptions():
    """The logged-in member's subscriptions (auth required)."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    conn = db()
    rows = conn.execute(
        "SELECT * FROM subscriptions WHERE user_id = ? ORDER BY id DESC",
        (user["id"],)).fetchall()
    conn.close()
    today = datetime.now(timezone.utc).date()
    out = []
    for r in rows:
        try:
            items = json.loads(r["items"] or "[]")
        except (TypeError, ValueError):
            items = []
        freq = SUB_FREQUENCIES.get(r["frequency"], {})
        disc = freq.get("discount", r["discount_percent"] or 0)
        try:
            days_until = (datetime.strptime(
                r["next_billing_date"], "%Y-%m-%d").date() - today).days
        except (TypeError, ValueError):
            days_until = 0
        out.append({
            "id": r["id"], "items": items, "frequency": r["frequency"],
            "frequency_label": freq.get("label", r["frequency"]),
            "discount_percent": disc, "status": r["status"],
            "next_billing_date": r["next_billing_date"],
            "per_delivery_cents": _per_delivery_cents(items, disc),
            "ship_state": r["ship_state"] or "", "ship_zip": r["ship_zip"] or "",
            "days_until_billing": days_until,
        })
    return jsonify(subscriptions=out)

@app.patch("/api/subscriptions/<int:sub_id>")
def update_subscription(sub_id):
    """Update a subscription (auth required, owner only)."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    data = request.get_json(force=True) or {}
    conn = db()
    sub = conn.execute(
        "SELECT * FROM subscriptions WHERE id = ? AND user_id = ?",
        (sub_id, user["id"])).fetchone()
    if not sub:
        conn.close()
        return jsonify(error="subscription not found"), 404
    sets = {}
    if "items" in data:
        items, err = _validate_subscription_items(data.get("items"))
        if err:
            conn.close()
            return err[0], err[1]
        sets["items"] = json.dumps(items)
    if "frequency" in data:
        frequency = (data.get("frequency") or "").strip()
        if frequency not in SUB_FREQUENCIES:
            conn.close()
            return jsonify(error="frequency must be biweekly, monthly, or bimonthly"), 400
        sets["frequency"] = frequency
        sets["discount_percent"] = SUB_FREQUENCIES[frequency]["discount"]
        sets["next_billing_date"] = (
            datetime.now(timezone.utc).date()
            + timedelta(days=SUB_FREQUENCIES[frequency]["days"])).isoformat()
    if "status" in data:
        st = (data.get("status") or "").strip().lower()
        cur = sub["status"]
        if st == "pause":
            if cur != "active":
                conn.close()
                return jsonify(error="only active subscriptions can be paused"), 400
            sets["status"] = "paused"
        elif st == "resume":
            if cur != "paused":
                conn.close()
                return jsonify(error="only paused subscriptions can be resumed"), 400
            sets["status"] = "active"
        elif st == "cancel":
            sets["status"] = "cancelled"
        else:
            conn.close()
            return jsonify(error="status must be pause, resume, or cancel"), 400
    if "shipping" in data:
        ship = data.get("shipping") or {}
        if not isinstance(ship, dict):
            conn.close()
            return jsonify(error="invalid shipping"), 400
        for key, col in (("name", "ship_name"), ("street", "ship_street"),
                         ("city", "ship_city"), ("state", "ship_state"),
                         ("zip", "ship_zip")):
            if key in ship:
                val = (ship.get(key) or "").strip()
                if key == "state":
                    val = val.upper()[:2]
                sets[col] = val[:200]
    if not sets:
        conn.close()
        return jsonify(error="nothing to update"), 400
    clause = ", ".join(f"{k} = ?" for k in sets)
    conn.execute(f"UPDATE subscriptions SET {clause} WHERE id = ?",
                 (*sets.values(), sub_id))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.get("/api/subscriptions/confirm/<token>")
def subscription_confirm_page(token):
    """Renewal confirmation page data (public)."""
    conn = db()
    ren = conn.execute(
        "SELECT * FROM subscription_renewals WHERE confirm_token = ?",
        ((token or "").strip(),)).fetchone()
    if not ren:
        conn.close()
        return jsonify(error="confirmation link not found"), 404
    sub = conn.execute(
        "SELECT * FROM subscriptions WHERE id = ?",
        (ren["subscription_id"],)).fetchone()
    if not sub:
        conn.close()
        return jsonify(error="subscription not found"), 404
    # The customer opened the link — record it.
    if ren["status"] == "reminded":
        conn.execute(
            "UPDATE subscription_renewals SET status = 'confirmed' WHERE id = ?",
            (ren["id"],))
        conn.commit()
    user = conn.execute(
        "SELECT name, email FROM users WHERE id = ?", (sub["user_id"],)).fetchone()
    try:
        items = json.loads(sub["items"] or "[]")
    except (TypeError, ValueError):
        items = []
    freq = SUB_FREQUENCIES.get(sub["frequency"], {})
    disc = freq.get("discount", sub["discount_percent"] or 0)
    per = _per_delivery_cents(items, disc)
    bags = sum(it["quantity"] for it in items if isinstance(it, dict))
    ship_est = _cheapest_shipping_cents(sub["ship_zip"], bags) if bags else 0
    ship_est = ship_est or 0
    conn.close()
    name = ""
    if user:
        name = user["name"] or sub["ship_name"] or ""
    else:
        name = sub["ship_name"] or ""
    return jsonify(
        subscription_id=sub["id"], name=name, items=items,
        frequency_label=freq.get("label", sub["frequency"]),
        billing_date=ren["billing_date"], per_delivery_cents=per,
        shipping_estimate_cents=ship_est, total_estimate_cents=per + ship_est,
        ship_state=sub["ship_state"] or "", ship_zip=sub["ship_zip"] or "")

@app.post("/api/subscriptions/confirm/<token>")
def subscription_confirm_charge(token):
    """Charge a renewal off-session (public, via the confirm link)."""
    data = request.get_json(force=True) or {}
    conn = db()
    ren = conn.execute(
        "SELECT * FROM subscription_renewals WHERE confirm_token = ?",
        ((token or "").strip(),)).fetchone()
    if not ren:
        conn.close()
        return jsonify(error="confirmation link not found"), 404
    if ren["status"] == "charged":
        conn.close()
        return jsonify(ok=True, already=True)
    sub = conn.execute(
        "SELECT * FROM subscriptions WHERE id = ?",
        (ren["subscription_id"],)).fetchone()
    if not sub or sub["status"] != "active":
        conn.close()
        return jsonify(error="subscription is not active"), 400
    if "items" in data and data.get("items") is not None:
        items, err = _validate_subscription_items(data.get("items"))
        if err:
            conn.close()
            return err[0], err[1]
        conn.execute("UPDATE subscriptions SET items = ? WHERE id = ?",
                     (json.dumps(items), sub["id"]))
        sub = conn.execute(
            "SELECT * FROM subscriptions WHERE id = ?", (sub["id"],)).fetchone()
    else:
        try:
            items = json.loads(sub["items"] or "[]")
        except (TypeError, ValueError):
            items = []
    ok, payload = _attempt_subscription_charge(conn, sub, ren, items)
    conn.commit()
    conn.close()
    if not ok:
        return payload[0], payload[1]
    notify_merchant_of_order(
        f"sub_{payload['payment_intent_id']}", sub["ship_name"],
        sub["ship_email"], payload["summary"], payload["amount"],
        "", 0, "", payload["ship_addr"],
        payload.get("label_url", ""), payload.get("tracking_number", ""))
    return jsonify(ok=True, order_number=payload["order_number"])

@app.post("/api/subscriptions/renewals/run")
def subscription_renewals_run():
    """Cron: send 3-day reminders and charge due renewals.

    Header X-Cron-Secret must equal the CRON_SECRET env var
    (503 when CRON_SECRET is not configured).
    """
    if not CRON_SECRET:
        return jsonify(error="cron is not configured"), 503
    if request.headers.get("X-Cron-Secret", "") != CRON_SECRET:
        return jsonify(error="forbidden"), 403
    today = datetime.now(timezone.utc).date()
    today_str = today.isoformat()
    target = (today + timedelta(days=3)).isoformat()
    reminded = charged = failed = 0
    conn = db()

    # 1) Reminders: active subscriptions billing in 3 days.
    subject, body = _subscription_template(conn)
    subs = conn.execute(
        "SELECT * FROM subscriptions WHERE status = 'active' AND next_billing_date = ?",
        (target,)).fetchall()
    for sub in subs:
        ren = conn.execute(
            "SELECT * FROM subscription_renewals"
            " WHERE subscription_id = ? AND billing_date = ?"
            " ORDER BY id DESC LIMIT 1",
            (sub["id"], target)).fetchone()
        if ren and ren["status"] in ("reminded", "confirmed", "charged", "failed"):
            continue
        if not ren:
            cur = conn.execute(
                "INSERT INTO subscription_renewals"
                " (subscription_id, billing_date, status, confirm_token)"
                " VALUES (?, ?, 'pending', ?)",
                (sub["id"], target, _new_confirm_token()))
            ren = conn.execute(
                "SELECT * FROM subscription_renewals WHERE id = ?",
                (cur.lastrowid,)).fetchone()
        to = sub["ship_email"] or ""
        if not to:
            continue
        try:
            items = json.loads(sub["items"] or "[]")
        except (TypeError, ValueError):
            items = []
        bags = sum(it["quantity"] for it in items if isinstance(it, dict))
        disc = SUB_FREQUENCIES.get(sub["frequency"], {}).get("discount", 0)
        per = _per_delivery_cents(items, disc)
        ship_est = _cheapest_shipping_cents(sub["ship_zip"], bags) if bags else 0
        ship_est = ship_est or 0
        user = conn.execute(
            "SELECT name FROM users WHERE id = ?", (sub["user_id"],)).fetchone()
        first = ((user["name"] or "").split()[0]
                 if user and user["name"] else "") or sub["ship_name"] or "there"
        ctx = {
            "name": first,
            "flavors": _items_summary_str(items),
            "billing_date": target,
            "confirm_url": f"{SITE_URL}/#subscription-confirm?token={ren['confirm_token']}",
            "bags": bags,
            "total": f"${(per + ship_est) / 100:,.2f}",
            "frequency_label": SUB_FREQUENCIES.get(
                sub["frequency"], {}).get("label", sub["frequency"]),
        }
        try:
            resp = requests.post(
                "https://api.resend.com/emails",
                headers={"Authorization": f"Bearer {RESEND_API_KEY}",
                         "Content-Type": "application/json"},
                json={
                    "from": "Pop-A-Licious Customer Service <customerservice@pop-a-licious.com>",
                    "to": [to],
                    "subject": _render_subscription_template(subject, ctx),
                    "html": _render_subscription_template(body, ctx),
                },
                timeout=15,
            )
            resp.raise_for_status()
        except Exception:
            continue  # leave pending; the next run retries
        conn.execute(
            "UPDATE subscription_renewals SET status = 'reminded', reminder_sent_at = ?"
            " WHERE id = ?",
            (datetime.now(timezone.utc).isoformat(), ren["id"]))
        conn.commit()
        reminded += 1

    # 2) Charges: renewals on/past their billing date, reminded/confirmed/failed (retry), not charged.
    dues = conn.execute(
        "SELECT id FROM subscription_renewals"
        " WHERE billing_date <= ? AND status IN ('reminded', 'confirmed', 'failed')"
        " AND failed_attempts < 3",
        (today_str,)).fetchall()
    for d in dues:
        ren = conn.execute(
            "SELECT * FROM subscription_renewals WHERE id = ?", (d["id"],)).fetchone()
        sub = conn.execute(
            "SELECT * FROM subscriptions WHERE id = ?",
            (ren["subscription_id"],)).fetchone()
        if not sub or sub["status"] != "active":
            continue
        try:
            items = json.loads(sub["items"] or "[]")
        except (TypeError, ValueError):
            items = []
        ok, payload = _attempt_subscription_charge(conn, sub, ren, items)
        conn.commit()
        if ok:
            charged += 1
            notify_merchant_of_order(
                f"sub_{payload['payment_intent_id']}", sub["ship_name"],
                sub["ship_email"], payload["summary"], payload["amount"],
                "", 0, "", payload["ship_addr"],
                payload.get("label_url", ""), payload.get("tracking_number", ""))
        else:
            failed += 1
    # 3) Anniversary kernels: 10 Kernels for members on their join-date anniversary.
    anniversaries = 0
    members = conn.execute(
        "SELECT id, created_at, anniversary_credited_year FROM users"
        " WHERE active = 1 AND verified = 1"
    ).fetchall()
    for m in members:
        try:
            joined = datetime.fromisoformat(m["created_at"])
        except Exception:
            continue
        if (joined.month, joined.day) == (today.month, today.day):
            if (m["anniversary_credited_year"] or 0) < today.year:
                _credit_kernels(conn, m["id"], 10, "anniversary",
                                order_ref=f"{today.year} anniversary")
                conn.execute(
                    "UPDATE users SET anniversary_credited_year = ? WHERE id = ?",
                    (today.year, m["id"]),
                )
                anniversaries += 1
    conn.commit()
    conn.close()
    return jsonify(reminded=reminded, charged=charged, failed=failed,
                   anniversaries=anniversaries)

# ---------------- admin: subscription email template ----------------

@app.get("/api/admin/subscription-email")
def admin_subscription_email_get():
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    subject, body = _subscription_template(conn)
    conn.close()
    return jsonify(subject=subject, body_html=body)

@app.put("/api/admin/subscription-email")
def admin_subscription_email_put():
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    data = request.get_json(force=True) or {}
    subject = (data.get("subject") or "").strip()
    body_html = data.get("body_html") or ""
    if not subject:
        return jsonify(error="subject is required"), 400
    if not body_html:
        return jsonify(error="body_html is required"), 400
    conn = db()
    conn.execute(
        """INSERT INTO subscription_email_templates (name, subject, body_html, updated_at)
           VALUES ('reminder', ?, ?, ?)
           ON CONFLICT(name) DO UPDATE SET subject = excluded.subject,
             body_html = excluded.body_html, updated_at = excluded.updated_at""",
        (subject, body_html, datetime.now(timezone.utc).isoformat()))
    conn.commit()
    conn.close()
    return jsonify(ok=True)

@app.post("/api/admin/subscription-email/preview")
def admin_subscription_email_preview():
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    data = request.get_json(force=True) or {}
    conn = db()
    subject, body = _subscription_template(conn)
    sub = None
    if data.get("subscription_id") is not None:
        try:
            sub = conn.execute(
                "SELECT * FROM subscriptions WHERE id = ?",
                (int(data.get("subscription_id")),)).fetchone()
        except (TypeError, ValueError):
            sub = None
    if sub:
        ren = conn.execute(
            "SELECT * FROM subscription_renewals WHERE subscription_id = ?"
            " ORDER BY id DESC LIMIT 1", (sub["id"],)).fetchone()
        token = ren["confirm_token"] if ren else "SAMPLE"
        try:
            items = json.loads(sub["items"] or "[]")
        except (TypeError, ValueError):
            items = []
        userrow = conn.execute(
            "SELECT name FROM users WHERE id = ?", (sub["user_id"],)).fetchone()
        first = ((userrow["name"] or "").split()[0]
                 if userrow and userrow["name"] else "") or sub["ship_name"] or "Alex"
        disc = SUB_FREQUENCIES.get(sub["frequency"], {}).get("discount", 0)
        ctx = {
            "name": first,
            "flavors": _items_summary_str(items) or "2x White Cheddar, 1x Caramel",
            "billing_date": sub["next_billing_date"],
            "confirm_url": f"{SITE_URL}/#subscription-confirm?token={token}",
            "bags": sum(it["quantity"] for it in items if isinstance(it, dict)),
            "total": f"${_per_delivery_cents(items, disc) / 100:,.2f}",
            "frequency_label": SUB_FREQUENCIES.get(
                sub["frequency"], {}).get("label", sub["frequency"]),
        }
    else:
        ctx = {
            "name": "Alex",
            "flavors": "2x White Cheddar, 1x Caramel",
            "billing_date": (datetime.now(timezone.utc).date()
                             + timedelta(days=3)).isoformat(),
            "confirm_url": f"{SITE_URL}/#subscription-confirm?token=SAMPLE",
            "bags": 3,
            "total": "$20.40",
            "frequency_label": "Every month",
        }
    conn.close()
    return jsonify(subject=_render_subscription_template(subject, ctx),
                   html=_render_subscription_template(body, ctx))


# ---------------- demo mode + subscription welcome email ----------------

SUBSCRIPTION_WELCOME_SUBJECT = "Welcome to the Pop-A-Licious Subscribe & Save Club! \U0001F37F"
_SUBSCRIPTION_WELCOME_FROM = "Pop-A-Licious Customer Service <customerservice@pop-a-licious.com>"
_FREQUENCY_EVERY = {"biweekly": "2 weeks", "monthly": "month", "bimonthly": "2 months"}

def _subscription_welcome_html(name, items, frequency, first_delivery_date):
    bags = sum(it["quantity"] for it in items if isinstance(it, dict))
    flavors = _items_summary_str(items)
    every = _FREQUENCY_EVERY.get(frequency, "month")
    try:
        d = datetime.fromisoformat(first_delivery_date).date()
        date_str = d.strftime("%B %d, %Y")
    except (TypeError, ValueError):
        date_str = first_delivery_date
    return f"""\
<html><body style="font-family: Arial, sans-serif; line-height: 1.6; color: #333;">
<p style="text-align:center;"><img src="https://pop-a-licious.com/logo.png" alt="Pop-A-Licious" style="max-width:220px;"></p>
<p>Hi {html.escape(name or 'there')},</p>
<p>Welcome to the <strong>Pop-A-Licious Subscribe &amp; Save Club</strong>! \U0001F37F<br>
Your popcorn is officially on autopilot.</p>
<p><strong>Your plan:</strong><br>
Bags per delivery: <strong>{bags}</strong><br>
Flavors: <strong>{html.escape(flavors)}</strong><br>
Frequency: <strong>{html.escape(SUB_FREQUENCIES.get(frequency, {}).get('label', frequency))}</strong></p>
<p>You'll receive your popcorn <strong>every {every} starting {html.escape(date_str)}</strong>.</p>
<p><strong>3 days before each delivery</strong>, we'll email you to confirm your flavors
&mdash; you can swap them anytime before we bill. No surprises, just popcorn.</p>
<p style="text-align:center;"><a href="{SITE_URL}/#my-subscriptions" style="display:inline-block;background:#e63946;color:#ffffff;text-decoration:none;padding:14px 28px;border-radius:8px;font-weight:bold;">Manage Your Subscription</a></p>
<p>Questions? Just reply to this email or write to us at customerservice@pop-a-licious.com.</p>
<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong><br>
2013 Angel Falls Dr., Henderson, NV 89074</p>
</body></html>"""

def _send_subscription_welcome_email(name, email, items, frequency, first_delivery_date):
    """Welcome email for a new subscription (real or demo). Never raises."""
    try:
        resp = requests.post(
            "https://api.resend.com/emails",
            headers={"Authorization": f"Bearer {RESEND_API_KEY}",
                     "Content-Type": "application/json"},
            json={
                "from": _SUBSCRIPTION_WELCOME_FROM,
                "to": [email],
                "subject": SUBSCRIPTION_WELCOME_SUBJECT,
                "html": _subscription_welcome_html(name, items, frequency,
                                                   first_delivery_date),
            },
            timeout=15,
        )
        resp.raise_for_status()
    except Exception:
        pass

def _demo_ref():
    return "demo_" + secrets.token_urlsafe(12)

@app.post("/api/demo/checkout")
def demo_checkout():
    """Demo-mode store checkout: same validation as the real checkout, but no
    Stripe, no Shippo label, no balance consumption. Order is saved with
    is_demo=1 and [DEMO] emails are sent."""
    data = request.get_json(force=True) or {}
    order, err = _compute_order(data)
    if err:
        return err[0], err[1]
    mark_abandoned_converted(data.get("email"))
    # Demo never consumes promo/gift-card/reward balances.
    total = order["merchandise_total"] + order["shipping_cents"]
    total -= order["gift_card_discount_cents"]
    total -= order["reward_discount_cents"]
    if order["promo_percent_off"]:
        total = int(round(total * (100 - order["promo_percent_off"]) / 100))
    total = max(total, 0)

    name = (data.get("name") or "").strip()[:120]
    shipping_address = (data.get("shipping_address") or "").strip()[:300]
    email = order["email"]
    session_ref = _demo_ref()
    now = datetime.now(timezone.utc).isoformat()
    total_qty = sum(it["quantity"] for it in order["items"])

    conn = db()
    cur = conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, total_qty, is_demo, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?)""",
        (session_ref, email, name, shipping_address, order["summary"], total,
         order["gift_card_code"], order["gift_card_discount_cents"],
         order["promo_code"], order["reward_code"], total_qty, now),
    )
    order_id = cur.lastrowid
    if email:
        urow = conn.execute(
            "SELECT id FROM users WHERE email = ?", (email,)).fetchone()
        if urow:
            _credit_kernels(conn, urow["id"],
                            total // 100 * KERNELS_PER_DOLLAR,
                            "purchase", order_ref=session_ref)
    conn.commit()
    conn.close()

    try:
        if email:
            send_email(
                email, "[DEMO] Your Pop-A-Licious order is confirmed!",
                order_email_html(name, order["summary"], total,
                                 order["gift_card_code"],
                                 order["gift_card_discount_cents"],
                                 order["promo_code"]))
    except Exception:
        pass
    try:
        notify_merchant_of_order("[DEMO] " + session_ref, name, email,
                                 order["summary"], total,
                                 order["gift_card_code"],
                                 order["gift_card_discount_cents"],
                                 order["promo_code"], shipping_address, "", "")
    except Exception:
        pass
    return jsonify(ok=True, demo=True, order_number=1000 + order_id,
                   order_ref=session_ref, total_cents=total)

@app.post("/api/demo/gift-card")
def demo_gift_card():
    """Demo-mode gift card purchase: validated like the real flow, no Stripe."""
    data = request.get_json(force=True) or {}
    try:
        amount = int(data.get("amount_cents", 0))
    except (TypeError, ValueError):
        return jsonify(error="amount_cents must be an integer number of cents"), 400
    purchaser_name = (data.get("purchaser_name") or "").strip()
    purchaser_email = (data.get("purchaser_email") or "").strip()
    recipient_name = (data.get("recipient_name") or "").strip()
    recipient_email = (data.get("recipient_email") or "").strip()
    message = (data.get("message") or "").strip()[:500]
    non_refundable_ok = bool(data.get("non_refundable_ack"))

    min_allowed = 50 if (ALLOW_TEST_AMOUNTS and amount == 50) else MIN_AMOUNT_CENTS
    if not (min_allowed <= amount <= MAX_AMOUNT_CENTS):
        min_str = "$0.50" if min_allowed == 50 else f"${min_allowed // 100}"
        return jsonify(error=f"amount must be between {min_str} and ${MAX_AMOUNT_CENTS // 100}"), 400
    if not purchaser_name or not EMAIL_RE.match(purchaser_email):
        return jsonify(error="valid purchaser name and email are required"), 400
    if not recipient_name or not EMAIL_RE.match(recipient_email):
        return jsonify(error="valid recipient name and email are required"), 400
    if not non_refundable_ok:
        return jsonify(error="please acknowledge the gift card is non-refundable"), 400

    code = issue_unique_code()
    session_ref = _demo_ref()
    now = datetime.now(timezone.utc).isoformat()
    conn = db()
    conn.execute(
        """INSERT INTO gift_cards
           (code, amount_cents, balance_cents, purchaser_name, purchaser_email,
            recipient_name, recipient_email, message, stripe_session_id,
            is_demo, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?)""",
        (code, amount, amount, purchaser_name, purchaser_email,
         recipient_name, recipient_email, message, session_ref, now),
    )
    conn.commit()
    conn.close()
    try:
        requests.post(
            "https://api.resend.com/emails",
            headers={"Authorization": f"Bearer {RESEND_API_KEY}",
                     "Content-Type": "application/json"},
            json={"from": EMAIL_FROM, "to": [recipient_email],
                  "subject": f"[DEMO] {purchaser_name} sent you a Pop-A-Licious gift card!",
                  "html": gift_card_email_html(purchaser_name, recipient_name,
                                               code, message)},
            timeout=15,
        ).raise_for_status()
    except Exception:
        pass
    return jsonify(ok=True, demo=True, code=code, amount_cents=amount)

@app.post("/api/demo/fundraiser-order")
def demo_fundraiser_order():
    """Demo-mode fundraiser supporter purchase: validated like the real flow,
    but no Stripe, no Shippo, no ticker entry, no sponsor matching."""
    data = request.get_json(force=True) or {}
    fcode = (data.get("fundraiser_code") or "").strip().upper()
    scode = (data.get("seller_referral_code") or "").strip().upper()
    customer_name = (data.get("customer_name") or "").strip()[:120]
    customer_email = (data.get("customer_email") or "").strip().lower()[:160]
    ship_name = (data.get("ship_name") or "").strip()[:120]
    ship_street = (data.get("ship_street") or "").strip()[:200]
    ship_city = (data.get("ship_city") or "").strip()[:120]
    ship_state = (data.get("ship_state") or "").strip().upper()[:2]
    ship_zip = (data.get("ship_zip") or "").strip()[:10]

    conn = db()
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE code = ?", (fcode,)).fetchone()
    if not fr:
        conn.close()
        return jsonify(error="fundraiser not found"), 404
    if fr["status"] != "active":
        conn.close()
        return jsonify(error="this fundraiser has ended"), 400
    seller_id = 0
    if scode:
        s = conn.execute(
            "SELECT id FROM fundraiser_sellers"
            " WHERE referral_code = ? AND fundraiser_id = ?",
            (scode, fr["id"])).fetchone()
        if not s:
            conn.close()
            return jsonify(error="seller not found"), 404
        seller_id = s["id"]
    conn.close()

    items, err = _validate_fundraiser_items(data.get("items"))
    if err:
        return err[0], err[1]
    total_qty = sum(it["quantity"] for it in items)
    subtotal = BAG_PRICE_CENTS * total_qty

    if not customer_name:
        return jsonify(error="your name is required"), 400
    if not EMAIL_RE.match(customer_email):
        return jsonify(error="a valid email is required"), 400
    if not ship_name or not ship_street or not ship_city or not ship_state or not ship_zip:
        return jsonify(error="a complete shipping address is required"), 400

    try:
        donation = int(data.get("donation_cents") or 0)
    except (TypeError, ValueError):
        return jsonify(error="donation_cents must be an integer"), 400
    if donation < 0 or donation > 100000:
        return jsonify(error="donation must be between $0 and $1,000"), 400
    roundup = 0
    if data.get("round_up") and subtotal % 100:
        roundup = (subtotal // 100 + 1) * 100 - subtotal

    ship_cents = _cheapest_shipping_cents(ship_zip, total_qty)
    if ship_cents is None:
        ship_cents = 0
    total = subtotal + donation + roundup + ship_cents
    if total < 50:
        return jsonify(error="order total is too small"), 400

    conn = db()
    try:
        order_number = _next_fundraiser_order_number(conn)
        session_ref = _demo_ref()
        now = datetime.now(timezone.utc).isoformat()
        conn.execute(
            """INSERT INTO fundraiser_orders
               (fundraiser_id, seller_id, order_number, customer_name, customer_email,
                ship_name, ship_street, ship_city, ship_state, ship_zip,
                items, subtotal_cents, donation_cents, roundup_cents,
                shipping_cents, total_cents, stripe_payment_intent_id, status,
                is_demo, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'paid', 1, ?)""",
            (fr["id"], seller_id, order_number, customer_name, customer_email,
             ship_name, ship_street, ship_city, ship_state, ship_zip,
             json.dumps(items), subtotal, donation, roundup, ship_cents, total,
             session_ref, now),
        )
    except RuntimeError:
        conn.close()
        return jsonify(error="could not record the order"), 500
    conn.commit()
    conn.close()

    dollars = lambda c: f"${c / 100:,.2f}"
    summary = _items_summary_str(items)
    try:
        if customer_email:
            send_email(
                customer_email,
                f"[DEMO] Thanks for supporting {fr['org_name']}!",
                '<html><body style="font-family: Arial, sans-serif; line-height: 1.6;">'
                f"<p>Hi {html.escape(customer_name) or 'there'},</p>"
                f"<p>Thanks for supporting <strong>{html.escape(fr['org_name'])}</strong>!"
                " Your fundraiser order is confirmed. &#x1F37F;</p>"
                f"<p><strong>Order:</strong> {html.escape(order_number)}"
                f"<br><strong>Items:</strong> {html.escape(summary)}"
                f"<br><strong>Donation:</strong> {dollars(donation)}</p>"
                f"<p><strong>Total charged:</strong> {dollars(total)}</p>"
                "<p>Stay delicious,<br><strong>The Pop-A-Licious Team</strong></p>"
                "</body></html>")
    except Exception:
        pass
    try:
        shipping = ", ".join(
            x for x in [ship_name, ship_street, ship_city, ship_state, ship_zip] if x)
        notify_merchant_of_order("[DEMO] " + order_number, customer_name,
                                 customer_email, summary, total, "", 0, "",
                                 shipping, "", "")
    except Exception:
        pass
    return jsonify(ok=True, demo=True, order_number=order_number)

@app.post("/api/demo/subscription")
def demo_subscription():
    """Demo-mode subscription signup: validated like the real flow, but no
    Stripe customer/payment-method calls. Sends the welcome email."""
    user = _current_member()
    if not user:
        return jsonify(error="login required"), 401
    data = request.get_json(force=True) or {}
    frequency = (data.get("frequency") or "").strip()
    ship = data.get("shipping") or {}
    if not isinstance(ship, dict):
        return jsonify(error="invalid shipping"), 400
    ship_name = (ship.get("name") or "").strip()[:120]
    ship_street = (ship.get("street") or "").strip()[:200]
    ship_city = (ship.get("city") or "").strip()[:120]
    ship_state = (ship.get("state") or "").strip().upper()[:2]
    ship_zip = (ship.get("zip") or "").strip()[:10]

    items, err = _validate_subscription_items(data.get("items"))
    if err:
        return err[0], err[1]
    if frequency not in SUB_FREQUENCIES:
        return jsonify(error="frequency must be biweekly, monthly, or bimonthly"), 400
    if not ship_name or not ship_street or not ship_city or not ship_state or not ship_zip:
        return jsonify(error="a complete shipping address is required"), 400

    conn = db()
    full = conn.execute(
        "SELECT * FROM users WHERE id = ?", (user["id"],)).fetchone()
    freq = SUB_FREQUENCIES[frequency]
    next_billing = (datetime.now(timezone.utc).date()
                    + timedelta(days=freq["days"])).isoformat()
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        """INSERT INTO subscriptions
           (user_id, stripe_customer_id, stripe_payment_method_id, items, frequency,
            discount_percent, status, next_billing_date,
            ship_name, ship_street, ship_city, ship_state, ship_zip, ship_email,
            is_demo, created_at)
           VALUES (?, 'demo', 'demo', ?, ?, ?, 'active', ?, ?, ?, ?, ?, ?, ?, 1, ?)""",
        (user["id"], json.dumps(items), frequency, freq["discount"], next_billing,
         ship_name, ship_street, ship_city, ship_state, ship_zip, full["email"],
         now))
    sub_id = cur.lastrowid
    conn.execute(
        "INSERT INTO subscription_renewals (subscription_id, billing_date, status, confirm_token)"
        " VALUES (?, ?, 'pending', ?)",
        (sub_id, next_billing, _new_confirm_token()))
    conn.commit()
    conn.close()
    _send_subscription_welcome_email(
        full["name"] or ship_name, full["email"], items, frequency, next_billing)
    return jsonify(id=sub_id, demo=True, next_billing_date=next_billing,
                   per_delivery_cents=_per_delivery_cents(items, freq["discount"]),
                   discount_percent=freq["discount"])

@app.get("/api/admin/demo/orders")
def admin_demo_orders():
    """List all demo-mode rows for the owner (admin only)."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    orders = conn.execute(
        "SELECT id, stripe_session_id, email, customer_name, items_summary,"
        " amount_total_cents, created_at FROM orders WHERE is_demo = 1"
        " ORDER BY id DESC").fetchall()
    fr_orders = conn.execute(
        "SELECT id, order_number, customer_email, total_cents, created_at"
        " FROM fundraiser_orders WHERE is_demo = 1 ORDER BY id DESC").fetchall()
    gift_cards = conn.execute(
        "SELECT code, amount_cents, purchaser_email, recipient_email, created_at"
        " FROM gift_cards WHERE is_demo = 1 ORDER BY created_at DESC").fetchall()
    subs = conn.execute(
        "SELECT id, frequency, next_billing_date, ship_email, created_at"
        " FROM subscriptions WHERE is_demo = 1 ORDER BY id DESC").fetchall()
    conn.close()
    return jsonify(
        orders=[dict(r) for r in orders],
        fundraiser_orders=[dict(r) for r in fr_orders],
        gift_cards=[dict(r) for r in gift_cards],
        subscriptions=[dict(r) for r in subs],
    )

@app.delete("/api/admin/demo/orders")
def admin_demo_cleanup():
    """Delete every demo-mode row (admin only). Real data is never touched."""
    user = _current_member()
    if not _is_admin(user):
        return jsonify(error="admin required"), 403
    conn = db()
    counts = {}
    counts["orders"] = conn.execute(
        "DELETE FROM orders WHERE is_demo = 1").rowcount
    counts["fundraiser_orders"] = conn.execute(
        "DELETE FROM fundraiser_orders WHERE is_demo = 1").rowcount
    counts["gift_cards"] = conn.execute(
        "DELETE FROM gift_cards WHERE is_demo = 1").rowcount
    sub_ids = [r["id"] for r in conn.execute(
        "SELECT id FROM subscriptions WHERE is_demo = 1").fetchall()]
    if sub_ids:
        q = ",".join("?" for _ in sub_ids)
        counts["subscription_renewals"] = conn.execute(
            f"DELETE FROM subscription_renewals WHERE subscription_id IN ({q})",
            sub_ids).rowcount
    else:
        counts["subscription_renewals"] = 0
    counts["subscriptions"] = conn.execute(
        "DELETE FROM subscriptions WHERE is_demo = 1").rowcount
    # Demo-credited Kernels (tagged with the demo order ref).
    counts["kernel_transactions"] = conn.execute(
        "DELETE FROM kernel_transactions WHERE order_ref LIKE 'demo\\_%' ESCAPE '\\'"
    ).rowcount
    conn.commit()
    conn.close()
    return jsonify(ok=True, deleted=counts)



# ---------------- Pop-A-Licious ERP — Phase 1: Inventory + Purchasing ----------------
# Made-to-order operation: finished popcorn is produced per order, so Phase 1
# tracks only ingredients, bags, front labels, and back labels. Every stock
# change is an immutable row in erp_stock_ledger; on-hand is SUM(qty_change).

ERP_ITEM_TYPES = ("ingredient", "bag", "front_label", "back_label")
ERP_ITEM_UNITS = ("lb", "oz", "bag", "each", "roll")
ERP_ADJUST_REASONS = ("count_correction", "damage", "spoilage", "sample",
                      "wholesale_shipment")
ERP_PO_STATUSES = ("draft", "sent", "partial", "received", "closed", "cancelled")
# Receiving auto-advances sent -> partial -> received; /status only handles
# the explicit human steps (send, cancel, close).
ERP_PO_TRANSITIONS = {
    "draft": ("sent", "cancelled"),
    "sent": ("cancelled",),
    "partial": ("cancelled",),
    "received": ("closed",),
    "closed": (),
    "cancelled": (),
}


def _erp_actor():
    """Identifies who performs an ERP action: admin email or 'staff:<name>'."""
    user = _current_member()
    if user and _is_admin(user):
        return user["email"]
    staff, _ = _require_staff()
    if staff:
        return "staff:" + (staff["name"] or staff["email"] or str(staff["id"]))
    return ""


# ---- ERP permission model (Phase 4 formalization; spec section 6) ----
# Two roles. "admin" (Matt/DJ) can do everything. "staff" can read inventory,
# recipes, batches, orders, wholesale accounts and EDI documents, and can
# perform inventory adjust/transfer/receive. Everything else — vendors, POs,
# costing, recipe/batch writes, wholesale writes, EDI writes, reports,
# QuickBooks — is admin-only.
# Behavior is unchanged from Phases 1-3; the matrix below just documents it
# in one place and every gate now routes through _erp_check_perm().
_ERP_PERMS = {
    "admin": frozenset({"*"}),
    "staff": frozenset({
        "erp.access",
        "inventory.read", "inventory.adjust", "inventory.transfer",
        "inventory.receive",
        "recipes.read", "batches.read",
        "orders.read", "accounts.read", "edi.read",
    }),
}


def _erp_role():
    """'admin', 'staff', 'wholesale', or None for the current request."""
    user = _current_member()
    if user and _is_admin(user):
        return "admin"
    staff, _ = _require_staff()
    if staff:
        return "staff"
    wuser, _ = _wholesale_user_from_request()
    if wuser:
        return "wholesale"
    return None


def _erp_check_perm(perm):
    """Single permission gate for ERP endpoints.

    Returns (actor, None) when allowed, else (None, (resp, code)).
    "admin" grants every permission. Status codes/messages match the
    pre-Phase-4 gates exactly (401 anon, 403 customer/staff as before).
    """
    role = _erp_role()
    if role == "admin":
        return _erp_actor(), None
    if role == "staff":
        if perm in _ERP_PERMS["staff"]:
            return _erp_actor(), None
        return None, (jsonify(error="admin required"), 403)
    if role == "wholesale":
        return None, (jsonify(error="not permitted for wholesale accounts"), 403)
    user = _current_member()
    if user:
        msg = "admin or staff required" if perm == "erp.access" else "admin required"
        return None, (jsonify(error=msg), 403)
    return None, (jsonify(error="login required"), 401)


def _require_erp():
    """Admin member OR staff. Returns (actor, None) or (None, (resp, code))."""
    return _erp_check_perm("erp.access")


def _require_erp_admin():
    """Admin member only (master data, POs, seed, reorder rules)."""
    return _erp_check_perm("admin")


def _erp_fmt_qty(q):
    s = ("%.4f" % float(q)).rstrip("0").rstrip(".")
    return s if s else "0"


def _erp_get_item(conn, item_id):
    try:
        item_id = int(item_id)
    except (TypeError, ValueError):
        return None
    return conn.execute("SELECT * FROM erp_items WHERE id = ?", (item_id,)).fetchone()


def _erp_get_location(conn, location_id):
    try:
        location_id = int(location_id)
    except (TypeError, ValueError):
        return None
    return conn.execute("SELECT * FROM erp_locations WHERE id = ?", (location_id,)).fetchone()


def _erp_get_location_by_code(conn, code):
    return conn.execute(
        "SELECT * FROM erp_locations WHERE code = ?", ((code or "").strip(),)).fetchone()


def _erp_on_hand(conn, item_id, location_id=None):
    if location_id is None:
        row = conn.execute(
            "SELECT COALESCE(SUM(qty_change), 0) AS q FROM erp_stock_ledger WHERE item_id = ?",
            (item_id,)).fetchone()
    else:
        row = conn.execute(
            "SELECT COALESCE(SUM(qty_change), 0) AS q FROM erp_stock_ledger"
            " WHERE item_id = ? AND location_id = ?",
            (item_id, location_id)).fetchone()
    return float(row["q"] or 0)


def _erp_post_movement(conn, item_id, location_id, qty_change, movement_type, actor,
                       ref_type="", ref_id="", lot_code="", unit_cost_cents=0, note=""):
    conn.execute(
        "INSERT INTO erp_stock_ledger (item_id, location_id, qty_change, movement_type,"
        " ref_type, ref_id, lot_code, unit_cost_cents, created_by, created_at, note)"
        " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        (item_id, location_id, float(qty_change), movement_type, ref_type, str(ref_id),
         lot_code, int(unit_cost_cents), actor,
         datetime.now(timezone.utc).isoformat(), note),
    )


def _erp_new_avg_cost(conn, item_id, received_qty, landed_unit_cost_cents):
    """Weighted-average cost, company-wide.

    new_avg = (old_qty * old_avg + received_qty * landed) / (old_qty + received_qty).
    Call BEFORE posting the receipt movement (reads current on-hand).
    """
    item = _erp_get_item(conn, item_id)
    old_avg = int(item["avg_cost_cents"] or 0)
    old_qty = _erp_on_hand(conn, item_id)
    denom = old_qty + received_qty
    if denom <= 0:
        return int(landed_unit_cost_cents)
    return int(round((old_qty * old_avg + received_qty * landed_unit_cost_cents) / denom))


def _erp_po_summary(conn, po):
    lines = conn.execute(
        "SELECT COUNT(*) AS n, COALESCE(SUM(qty_ordered * unit_cost_cents), 0) AS ordered,"
        " COALESCE(SUM(qty_received * unit_cost_cents), 0) AS received"
        " FROM erp_po_lines WHERE po_id = ?", (po["id"],)).fetchone()
    vendor = conn.execute(
        "SELECT name FROM erp_vendors WHERE id = ?", (po["vendor_id"],)).fetchone()
    d = dict(po)
    d["vendor_name"] = vendor["name"] if vendor else ""
    d["line_count"] = lines["n"]
    d["total_ordered_cents"] = int(lines["ordered"] or 0)
    d["total_received_cents"] = int(lines["received"] or 0)
    return d


@app.get("/api/erp/locations")
def erp_list_locations():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    rows = conn.execute(
        "SELECT * FROM erp_locations WHERE active = 1 ORDER BY id").fetchall()
    conn.close()
    return jsonify(locations=[dict(r) for r in rows])


@app.get("/api/erp/items")
def erp_list_items():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    if request.args.get("include_inactive") == "1":
        rows = conn.execute("SELECT * FROM erp_items ORDER BY type, name").fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM erp_items WHERE active = 1 ORDER BY type, name").fetchall()
    conn.close()
    return jsonify(items=[dict(r) for r in rows])


@app.post("/api/erp/items")
def erp_create_item():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    sku = (data.get("sku") or "").strip()
    name = (data.get("name") or "").strip()
    itype = (data.get("type") or "").strip()
    unit = (data.get("unit") or "each").strip()
    track_lots = 1 if data.get("track_lots") else 0
    if not sku or not name:
        return jsonify(error="sku and name are required"), 400
    if itype not in ERP_ITEM_TYPES:
        return jsonify(error="type must be one of: " + ", ".join(ERP_ITEM_TYPES)), 400
    if unit not in ERP_ITEM_UNITS:
        return jsonify(error="unit must be one of: " + ", ".join(ERP_ITEM_UNITS)), 400
    conn = db()
    if conn.execute("SELECT 1 FROM erp_items WHERE sku = ?", (sku,)).fetchone():
        conn.close()
        return jsonify(error="sku already exists"), 400
    cur = conn.execute(
        "INSERT INTO erp_items (sku, name, type, unit, track_lots, avg_cost_cents,"
        " active, created_at) VALUES (?, ?, ?, ?, ?, 0, 1, ?)",
        (sku, name, itype, unit, track_lots, datetime.now(timezone.utc).isoformat()),
    )
    item_id = cur.lastrowid
    conn.commit()
    row = conn.execute("SELECT * FROM erp_items WHERE id = ?", (item_id,)).fetchone()
    conn.close()
    return jsonify(item=dict(row)), 201


@app.get("/api/erp/items/<int:item_id>")
def erp_get_item(item_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    item = _erp_get_item(conn, item_id)
    if not item:
        conn.close()
        return jsonify(error="item not found"), 404
    locs = conn.execute(
        "SELECT * FROM erp_locations WHERE active = 1 ORDER BY id").fetchall()
    stock = [
        {"location_id": loc["id"], "location_code": loc["code"],
         "location_name": loc["name"],
         "on_hand": _erp_on_hand(conn, item["id"], loc["id"])}
        for loc in locs
    ]
    ledger = conn.execute(
        "SELECT l.*, loc.code AS location_code FROM erp_stock_ledger l"
        " LEFT JOIN erp_locations loc ON loc.id = l.location_id"
        " WHERE l.item_id = ? ORDER BY l.id DESC LIMIT 50",
        (item["id"],)).fetchall()
    conn.close()
    d = dict(item)
    d["stock_by_location"] = stock
    d["on_hand_total"] = sum(s["on_hand"] for s in stock)
    d["ledger"] = [dict(r) for r in ledger]
    return jsonify(item=d)


@app.get("/api/erp/stock")
def erp_stock():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    type_filter = (request.args.get("type") or "").strip()
    loc_filter = (request.args.get("location_id") or "").strip()
    items = conn.execute(
        "SELECT * FROM erp_items WHERE active = 1 ORDER BY type, name").fetchall()
    locs = conn.execute(
        "SELECT * FROM erp_locations WHERE active = 1 ORDER BY id").fetchall()
    rows = []
    for it in items:
        if type_filter and it["type"] != type_filter:
            continue
        avg = int(it["avg_cost_cents"] or 0)
        for loc in locs:
            if loc_filter and str(loc["id"]) != loc_filter:
                continue
            q = _erp_on_hand(conn, it["id"], loc["id"])
            rows.append({
                "item_id": it["id"], "sku": it["sku"], "name": it["name"],
                "type": it["type"], "unit": it["unit"], "avg_cost_cents": avg,
                "location_id": loc["id"], "location_code": loc["code"],
                "location_name": loc["name"], "on_hand": q,
                "value_cents": int(round(q * avg)),
            })
    conn.close()
    return jsonify(stock=rows)


@app.get("/api/erp/ledger")
def erp_ledger():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    clauses, params = [], []
    item_id = request.args.get("item_id")
    location_id = request.args.get("location_id")
    if item_id:
        clauses.append("l.item_id = ?")
        params.append(int(item_id))
    if location_id:
        clauses.append("l.location_id = ?")
        params.append(int(location_id))
    try:
        limit = min(int(request.args.get("limit", 100)), 500)
    except (TypeError, ValueError):
        limit = 100
    where = (" WHERE " + " AND ".join(clauses)) if clauses else ""
    rows = conn.execute(
        "SELECT l.*, i.sku, i.name AS item_name, loc.code AS location_code"
        " FROM erp_stock_ledger l"
        " LEFT JOIN erp_items i ON i.id = l.item_id"
        " LEFT JOIN erp_locations loc ON loc.id = l.location_id"
        + where + " ORDER BY l.id DESC LIMIT ?",
        params + [limit]).fetchall()
    conn.close()
    return jsonify(movements=[dict(r) for r in rows])


@app.post("/api/erp/adjust")
def erp_adjust():
    actor, err = _require_erp()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    item = _erp_get_item(conn, data.get("item_id"))
    if not item or not item["active"]:
        conn.close()
        return jsonify(error="valid item_id is required"), 400
    loc = _erp_get_location(conn, data.get("location_id"))
    if not loc or not loc["active"]:
        conn.close()
        return jsonify(error="valid location_id is required"), 400
    try:
        qty = float(data.get("qty_change") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="qty_change must be a number"), 400
    if qty == 0:
        conn.close()
        return jsonify(error="qty_change cannot be zero"), 400
    reason = (data.get("reason") or "").strip()
    if reason not in ERP_ADJUST_REASONS:
        conn.close()
        return jsonify(error="reason must be one of: " + ", ".join(ERP_ADJUST_REASONS)), 400
    note = (data.get("note") or "").strip()
    _erp_post_movement(conn, item["id"], loc["id"], qty, "adjustment", actor,
                       ref_type="reason", ref_id=reason,
                       unit_cost_cents=int(item["avg_cost_cents"] or 0), note=note)
    conn.commit()
    on_hand = _erp_on_hand(conn, item["id"], loc["id"])
    conn.close()
    return jsonify(ok=True, item_id=item["id"], location_id=loc["id"],
                   on_hand=on_hand, reason=reason)


@app.post("/api/erp/transfer")
def erp_transfer():
    actor, err = _require_erp()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    item = _erp_get_item(conn, data.get("item_id"))
    if not item or not item["active"]:
        conn.close()
        return jsonify(error="valid item_id is required"), 400
    src = _erp_get_location(conn, data.get("from_location_id"))
    dst = _erp_get_location(conn, data.get("to_location_id"))
    if not src or not src["active"] or not dst or not dst["active"]:
        conn.close()
        return jsonify(error="valid from_location_id and to_location_id are required"), 400
    if src["id"] == dst["id"]:
        conn.close()
        return jsonify(error="source and destination must differ"), 400
    try:
        qty = float(data.get("qty") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="qty must be a number"), 400
    if qty <= 0:
        conn.close()
        return jsonify(error="qty must be greater than zero"), 400
    available = _erp_on_hand(conn, item["id"], src["id"])
    if available + 1e-9 < qty:
        conn.close()
        return jsonify(error="insufficient stock at %s (have %s, need %s)"
                              % (src["code"], _erp_fmt_qty(available), _erp_fmt_qty(qty))), 400
    group = "TR-" + secrets.token_hex(4).upper()
    avg = int(item["avg_cost_cents"] or 0)
    note = (data.get("note") or "").strip()
    _erp_post_movement(conn, item["id"], src["id"], -qty, "transfer_out", actor,
                       ref_type="transfer", ref_id=group, unit_cost_cents=avg, note=note)
    _erp_post_movement(conn, item["id"], dst["id"], qty, "transfer_in", actor,
                       ref_type="transfer", ref_id=group, unit_cost_cents=avg, note=note)
    conn.commit()
    conn.close()
    return jsonify(ok=True, transfer_ref=group, item_id=item["id"],
                   from_location_id=src["id"], to_location_id=dst["id"], qty=qty)


@app.get("/api/erp/vendors")
def erp_list_vendors():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    if request.args.get("include_inactive") == "1":
        rows = conn.execute("SELECT * FROM erp_vendors ORDER BY name").fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM erp_vendors WHERE active = 1 ORDER BY name").fetchall()
    conn.close()
    return jsonify(vendors=[dict(r) for r in rows])


@app.post("/api/erp/vendors")
def erp_create_vendor():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()
    if not name:
        return jsonify(error="name is required"), 400
    try:
        lead_time = int(data.get("lead_time_days") or 0)
    except (TypeError, ValueError):
        lead_time = 0
    conn = db()
    cur = conn.execute(
        "INSERT INTO erp_vendors (name, contact_name, email, phone, payment_terms,"
        " lead_time_days, notes, active, created_at)"
        " VALUES (?, ?, ?, ?, ?, ?, ?, 1, ?)",
        (name, (data.get("contact_name") or "").strip(),
         (data.get("email") or "").strip(), (data.get("phone") or "").strip(),
         (data.get("payment_terms") or "").strip(), max(lead_time, 0),
         (data.get("notes") or "").strip(), datetime.now(timezone.utc).isoformat()),
    )
    vendor_id = cur.lastrowid
    conn.commit()
    row = conn.execute("SELECT * FROM erp_vendors WHERE id = ?", (vendor_id,)).fetchone()
    conn.close()
    return jsonify(vendor=dict(row)), 201


@app.post("/api/erp/vendors/<int:vendor_id>/deactivate")
def erp_deactivate_vendor(vendor_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    vendor = conn.execute(
        "SELECT * FROM erp_vendors WHERE id = ?", (vendor_id,)).fetchone()
    if not vendor:
        conn.close()
        return jsonify(error="vendor not found"), 404
    conn.execute("UPDATE erp_vendors SET active = 0 WHERE id = ?", (vendor_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True, vendor_id=vendor_id)


@app.get("/api/erp/purchase-orders")
def erp_list_pos():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    status = (request.args.get("status") or "").strip()
    if status and status in ERP_PO_STATUSES:
        rows = conn.execute(
            "SELECT * FROM erp_purchase_orders WHERE status = ? ORDER BY id DESC",
            (status,)).fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM erp_purchase_orders ORDER BY id DESC").fetchall()
    result = [_erp_po_summary(conn, po) for po in rows]
    conn.close()
    return jsonify(purchase_orders=result)


@app.post("/api/erp/purchase-orders")
def erp_create_po():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    try:
        vendor_id = int(data.get("vendor_id") or 0)
    except (TypeError, ValueError):
        vendor_id = 0
    vendor = conn.execute(
        "SELECT * FROM erp_vendors WHERE id = ?", (vendor_id,)).fetchone()
    if not vendor or not vendor["active"]:
        conn.close()
        return jsonify(error="valid vendor_id is required"), 400
    raw_lines = data.get("lines") or []
    if not raw_lines:
        conn.close()
        return jsonify(error="at least one line is required"), 400
    clean = []
    for entry in raw_lines:
        item = _erp_get_item(conn, (entry or {}).get("item_id"))
        if not item or not item["active"]:
            conn.close()
            return jsonify(error="every line needs a valid item_id"), 400
        try:
            qty = float(entry.get("qty_ordered") or 0)
        except (TypeError, ValueError):
            qty = 0
        try:
            cost = int(entry.get("unit_cost_cents") or 0)
        except (TypeError, ValueError):
            cost = 0
        if qty <= 0:
            conn.close()
            return jsonify(error="qty_ordered must be greater than zero"), 400
        if cost < 0:
            conn.close()
            return jsonify(error="unit_cost_cents cannot be negative"), 400
        clean.append((item["id"], qty, cost))
    try:
        freight = int(data.get("freight_cents") or 0)
        tax = int(data.get("tax_cents") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="freight_cents and tax_cents must be whole cents"), 400
    if freight < 0 or tax < 0:
        conn.close()
        return jsonify(error="freight_cents and tax_cents cannot be negative"), 400
    count = conn.execute("SELECT COUNT(*) AS c FROM erp_purchase_orders").fetchone()["c"]
    po_number = "PO-%d" % (1001 + int(count))
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_purchase_orders (po_number, vendor_id, status, order_date,"
        " expected_date, freight_cents, tax_cents, notes, created_by, created_at)"
        " VALUES (?, ?, 'draft', ?, ?, ?, ?, ?, ?, ?)",
        (po_number, vendor["id"], now[:10],
         (data.get("expected_date") or "").strip(), freight, tax,
         (data.get("notes") or "").strip(), actor, now),
    )
    po_id = cur.lastrowid
    for item_id, qty, cost in clean:
        conn.execute(
            "INSERT INTO erp_po_lines (po_id, item_id, qty_ordered, qty_received,"
            " unit_cost_cents) VALUES (?, ?, ?, 0, ?)",
            (po_id, item_id, qty, cost),
        )
    conn.commit()
    po = conn.execute(
        "SELECT * FROM erp_purchase_orders WHERE id = ?", (po_id,)).fetchone()
    result = _erp_po_summary(conn, po)
    conn.close()
    return jsonify(purchase_order=result), 201


@app.get("/api/erp/purchase-orders/<int:po_id>")
def erp_get_po(po_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    po = conn.execute(
        "SELECT * FROM erp_purchase_orders WHERE id = ?", (po_id,)).fetchone()
    if not po:
        conn.close()
        return jsonify(error="purchase order not found"), 404
    vendor = conn.execute(
        "SELECT * FROM erp_vendors WHERE id = ?", (po["vendor_id"],)).fetchone()
    lines = conn.execute(
        "SELECT l.*, i.sku, i.name AS item_name, i.type AS item_type, i.unit AS item_unit"
        " FROM erp_po_lines l JOIN erp_items i ON i.id = l.item_id"
        " WHERE l.po_id = ? ORDER BY l.id", (po_id,)).fetchall()
    summary = _erp_po_summary(conn, po)
    conn.close()
    return jsonify(purchase_order=summary, vendor=dict(vendor) if vendor else None,
                   lines=[dict(l) for l in lines])


@app.post("/api/erp/purchase-orders/<int:po_id>/receive")
def erp_po_receive(po_id):
    actor, err = _require_erp()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    po = conn.execute(
        "SELECT * FROM erp_purchase_orders WHERE id = ?", (po_id,)).fetchone()
    if not po:
        conn.close()
        return jsonify(error="purchase order not found"), 404
    if po["status"] not in ("sent", "partial"):
        conn.close()
        return jsonify(
            error="PO must be sent before receiving (status: %s)" % po["status"]), 400
    lines = conn.execute(
        "SELECT * FROM erp_po_lines WHERE po_id = ? ORDER BY id",
        (po_id,)).fetchall()
    by_id = {l["id"]: l for l in lines}
    req_lines = data.get("lines") or []
    if not req_lines:
        conn.close()
        return jsonify(error="lines is required"), 400
    location_id = data.get("location_id")
    if location_id is None:
        hend = _erp_get_location_by_code(conn, "HEND")
        location_id = hend["id"] if hend else None
    loc = _erp_get_location(conn, location_id)
    if not loc or not loc["active"]:
        conn.close()
        return jsonify(error="valid location_id is required"), 400
    lot_code_in = (data.get("lot_code") or "").strip()
    expiry_date = (data.get("expiry_date") or "").strip()
    # Validate everything before writing (all-or-nothing).
    todo = []
    for entry in req_lines:
        try:
            line_id = int((entry or {}).get("line_id") or 0)
        except (TypeError, ValueError):
            line_id = 0
        line = by_id.get(line_id)
        if not line:
            conn.close()
            return jsonify(error="PO line not found"), 400
        try:
            qty = float(entry.get("qty_received") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="qty_received must be a number"), 400
        remaining = float(line["qty_ordered"]) - float(line["qty_received"])
        if qty <= 0 or qty > remaining + 1e-9:
            conn.close()
            return jsonify(
                error="qty_received for line %d must be between 0 and %s"
                      % (line["id"], _erp_fmt_qty(remaining))), 400
        todo.append((line, qty))
    total_ordered_value = sum(
        float(l["qty_ordered"]) * int(l["unit_cost_cents"]) for l in lines)
    total_receipt_qty = sum(qty for _, qty in todo)
    freight = int(po["freight_cents"] or 0)
    today = datetime.now(timezone.utc).date().isoformat()
    received = []
    for line, qty in todo:
        unit_cost = int(line["unit_cost_cents"])
        if total_ordered_value > 0:
            alloc = freight * (qty * unit_cost) / total_ordered_value
        elif total_receipt_qty > 0:
            alloc = freight * qty / total_receipt_qty
        else:
            alloc = 0
        landed = unit_cost + int(round(alloc / qty)) if qty else unit_cost
        new_avg = _erp_new_avg_cost(conn, line["item_id"], qty, landed)
        lot_code = lot_code_in or ("%s-L%d" % (po["po_number"], line["id"]))
        _erp_post_movement(conn, line["item_id"], loc["id"], qty, "purchase_receipt",
                           actor, ref_type="po", ref_id=po["po_number"],
                           lot_code=lot_code, unit_cost_cents=landed,
                           note="PO %s receive" % po["po_number"])
        conn.execute("UPDATE erp_items SET avg_cost_cents = ? WHERE id = ?",
                     (new_avg, line["item_id"]))
        conn.execute("UPDATE erp_po_lines SET qty_received = qty_received + ? WHERE id = ?",
                     (qty, line["id"]))
        if lot_code or expiry_date:
            conn.execute(
                "INSERT INTO erp_lots (lot_code, item_id, supplier_lot, received_date,"
                " expiry_date, location_id) VALUES (?, ?, '', ?, ?, ?)",
                (lot_code, line["item_id"], today, expiry_date, loc["id"]),
            )
        received.append({"line_id": line["id"], "qty_received": qty,
                         "landed_unit_cost_cents": landed,
                         "new_avg_cost_cents": new_avg})
    remaining_total = conn.execute(
        "SELECT COALESCE(SUM(qty_ordered - qty_received), 0) AS r"
        " FROM erp_po_lines WHERE po_id = ?", (po_id,)).fetchone()["r"]
    new_status = "received" if float(remaining_total or 0) <= 1e-9 else "partial"
    conn.execute("UPDATE erp_purchase_orders SET status = ? WHERE id = ?",
                 (new_status, po_id))
    conn.commit()
    conn.close()
    return jsonify(ok=True, po_id=po_id, status=new_status, received=received)


@app.post("/api/erp/purchase-orders/<int:po_id>/status")
def erp_po_status(po_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    new_status = (data.get("status") or "").strip()
    if new_status not in ERP_PO_STATUSES:
        return jsonify(error="status must be one of: " + ", ".join(ERP_PO_STATUSES)), 400
    conn = db()
    po = conn.execute(
        "SELECT * FROM erp_purchase_orders WHERE id = ?", (po_id,)).fetchone()
    if not po:
        conn.close()
        return jsonify(error="purchase order not found"), 404
    allowed = ERP_PO_TRANSITIONS.get(po["status"], ())
    if new_status not in allowed:
        conn.close()
        return jsonify(error="cannot move PO from %s to %s" % (po["status"], new_status)), 400
    conn.execute("UPDATE erp_purchase_orders SET status = ? WHERE id = ?",
                 (new_status, po_id))
    conn.commit()
    conn.close()
    return jsonify(ok=True, po_id=po_id, status=new_status)


@app.get("/api/erp/reorder-rules")
def erp_list_reorder_rules():
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    rows = conn.execute(
        "SELECT r.*, i.sku, i.name AS item_name, l.code AS location_code,"
        " v.name AS vendor_name FROM erp_reorder_rules r"
        " JOIN erp_items i ON i.id = r.item_id"
        " JOIN erp_locations l ON l.id = r.location_id"
        " LEFT JOIN erp_vendors v ON v.id = r.preferred_vendor_id"
        " ORDER BY i.name").fetchall()
    conn.close()
    return jsonify(reorder_rules=[dict(r) for r in rows])


@app.post("/api/erp/reorder-rules")
def erp_upsert_reorder_rule():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    item = _erp_get_item(conn, data.get("item_id"))
    loc = _erp_get_location(conn, data.get("location_id"))
    if not item or not item["active"] or not loc or not loc["active"]:
        conn.close()
        return jsonify(error="valid item_id and location_id are required"), 400
    try:
        reorder_point = float(data.get("reorder_point"))
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="reorder_point must be a number"), 400
    try:
        reorder_qty = float(data.get("reorder_qty") or 0)
    except (TypeError, ValueError):
        reorder_qty = 0
    vendor_id = data.get("preferred_vendor_id") or 0
    try:
        vendor_id = int(vendor_id)
    except (TypeError, ValueError):
        vendor_id = 0
    if vendor_id and not conn.execute(
            "SELECT 1 FROM erp_vendors WHERE id = ?", (vendor_id,)).fetchone():
        conn.close()
        return jsonify(error="preferred_vendor_id not found"), 400
    existing = conn.execute(
        "SELECT id FROM erp_reorder_rules WHERE item_id = ? AND location_id = ?",
        (item["id"], loc["id"])).fetchone()
    now = datetime.now(timezone.utc).isoformat()
    if existing:
        conn.execute(
            "UPDATE erp_reorder_rules SET reorder_point = ?, reorder_qty = ?,"
            " preferred_vendor_id = ? WHERE id = ?",
            (reorder_point, reorder_qty, vendor_id, existing["id"]))
        rule_id = existing["id"]
    else:
        cur = conn.execute(
            "INSERT INTO erp_reorder_rules (item_id, location_id, reorder_point,"
            " reorder_qty, preferred_vendor_id, created_at)"
            " VALUES (?, ?, ?, ?, ?, ?)",
            (item["id"], loc["id"], reorder_point, reorder_qty, vendor_id, now))
        rule_id = cur.lastrowid
    conn.commit()
    row = conn.execute(
        "SELECT * FROM erp_reorder_rules WHERE id = ?", (rule_id,)).fetchone()
    conn.close()
    return jsonify(reorder_rule=dict(row))


@app.get("/api/erp/alerts/low-stock")
def erp_low_stock():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    rules = conn.execute(
        "SELECT r.*, i.sku, i.name AS item_name, i.unit, l.code AS location_code"
        " FROM erp_reorder_rules r"
        " JOIN erp_items i ON i.id = r.item_id"
        " JOIN erp_locations l ON l.id = r.location_id").fetchall()
    alerts = []
    for r in rules:
        on_hand = _erp_on_hand(conn, r["item_id"], r["location_id"])
        if on_hand <= float(r["reorder_point"]):
            alerts.append({
                "item_id": r["item_id"], "sku": r["sku"], "item_name": r["item_name"],
                "unit": r["unit"], "location_id": r["location_id"],
                "location_code": r["location_code"], "on_hand": on_hand,
                "reorder_point": float(r["reorder_point"]),
                "reorder_qty": float(r["reorder_qty"]),
                "preferred_vendor_id": r["preferred_vendor_id"],
            })
    conn.close()
    return jsonify(alerts=alerts, count=len(alerts))


@app.post("/api/erp/seed")
def erp_seed():
    """One-time import of opening balances. Refuses to run twice."""
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    already = conn.execute(
        "SELECT 1 FROM erp_stock_ledger WHERE movement_type = 'opening_balance'"
        " LIMIT 1").fetchone()
    if already:
        conn.close()
        return jsonify(error="opening balances have already been seeded"), 400
    rows = data.get("rows") or []
    if not rows:
        conn.close()
        return jsonify(error="rows is required"), 400
    # Validate everything before writing (all-or-nothing).
    plan = []
    for n, entry in enumerate(rows, 1):
        entry = entry or {}
        item = conn.execute(
            "SELECT * FROM erp_items WHERE sku = ?", ((entry.get("sku") or "").strip(),)
        ).fetchone()
        if not item or not item["active"]:
            conn.close()
            return jsonify(error="row %d: unknown sku '%s'" % (n, entry.get("sku"))), 400
        loc = _erp_get_location_by_code(conn, entry.get("location_code"))
        if not loc or not loc["active"]:
            conn.close()
            return jsonify(error="row %d: unknown location_code '%s'"
                                 % (n, entry.get("location_code"))), 400
        try:
            qty = float(entry.get("qty") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="row %d: qty must be a number" % n), 400
        if qty <= 0:
            conn.close()
            return jsonify(error="row %d: qty must be greater than zero" % n), 400
        try:
            cost = int(entry.get("unit_cost_cents") or 0)
        except (TypeError, ValueError):
            cost = 0
        plan.append((item, loc, qty,
                     (entry.get("lot_code") or "").strip(),
                     (entry.get("expiry_date") or "").strip(), cost))
    today = datetime.now(timezone.utc).date().isoformat()
    for item, loc, qty, lot_code, expiry_date, cost in plan:
        if cost > 0:
            new_avg = _erp_new_avg_cost(conn, item["id"], qty, cost)
        else:
            new_avg = None
        _erp_post_movement(conn, item["id"], loc["id"], qty, "opening_balance", actor,
                           unit_cost_cents=cost, lot_code=lot_code,
                           note="Opening balance seed")
        if new_avg is not None:
            conn.execute("UPDATE erp_items SET avg_cost_cents = ? WHERE id = ?",
                         (new_avg, item["id"]))
        if lot_code or expiry_date:
            conn.execute(
                "INSERT INTO erp_lots (lot_code, item_id, supplier_lot, received_date,"
                " expiry_date, location_id) VALUES (?, ?, '', ?, ?, ?)",
                (lot_code, item["id"], today, expiry_date, loc["id"]),
            )
    conn.commit()
    conn.close()
    return jsonify(ok=True, imported=len(plan))


# ---------------- ERP Phase 2: Production ----------------
# Recipes, production batches, lot traceability. Builds on the Phase 1
# immutable ledger: completing a batch posts production_out movements.
# (Tables are created in init_db() above.)

ERP_BATCH_STATUSES = ("planned", "in_progress", "completed", "cancelled",
                      "reversed")


def _erp_get_recipe(conn, recipe_id):
    try:
        recipe_id = int(recipe_id)
    except (TypeError, ValueError):
        return None
    return conn.execute("SELECT * FROM erp_recipes WHERE id = ?",
                        (recipe_id,)).fetchone()


def _erp_recipe_lines(conn, recipe_id, version):
    return conn.execute(
        "SELECT rl.*, i.sku, i.name AS item_name, i.type AS item_type,"
        " i.unit AS item_unit FROM erp_recipe_lines rl"
        " JOIN erp_items i ON i.id = rl.item_id"
        " WHERE rl.recipe_id = ? AND rl.recipe_version = ? ORDER BY rl.id",
        (recipe_id, version)).fetchall()


def _erp_get_batch(conn, batch_id):
    try:
        batch_id = int(batch_id)
    except (TypeError, ValueError):
        return None
    return conn.execute("SELECT * FROM erp_production_batches WHERE id = ?",
                        (batch_id,)).fetchone()


def _erp_lot_balances(conn, item_id, location_id):
    """FIFO-ordered lot balances for an item at a location, from the ledger.

    Returns [(lot_code, on_hand, first_seen), ...], oldest first.
    Stock without a lot code is not listed here (handled as remainder).
    """
    rows = conn.execute(
        "SELECT lot_code, COALESCE(SUM(qty_change), 0) AS q,"
        " MIN(created_at) AS first_seen FROM erp_stock_ledger"
        " WHERE item_id = ? AND location_id = ? AND lot_code != ''"
        " GROUP BY lot_code HAVING q > 1e-9 ORDER BY first_seen",
        (item_id, location_id)).fetchall()
    return [(r["lot_code"], float(r["q"]), r["first_seen"]) for r in rows]


def _erp_expiry_plus_months(date_str, months):
    """'YYYY-MM-DD' + months -> 'YYYY-MM-DD', day clamped to month end."""
    import calendar
    y, m, d = (int(x) for x in date_str.split("-"))
    m += months
    y += (m - 1) // 12
    m = (m - 1) % 12 + 1
    d = min(d, calendar.monthrange(y, m)[1])
    return "%04d-%02d-%02d" % (y, m, d)


def _erp_validate_recipe_lines(conn, lines):
    """Validate recipe lines. Returns (clean_lines, error)."""
    clean = []
    seen = set()
    for n, ln in enumerate(lines or [], 1):
        ln = ln or {}
        item = _erp_get_item(conn, ln.get("item_id"))
        if not item or not item["active"]:
            return None, "line %d: valid item_id is required" % n
        if item["id"] in seen:
            return None, "line %d: duplicate item '%s'" % (n, item["sku"])
        seen.add(item["id"])
        try:
            qty = float(ln.get("qty_per_batch") or 0)
        except (TypeError, ValueError):
            return None, "line %d: qty_per_batch must be a number" % n
        if qty <= 0:
            return None, "line %d: qty_per_batch must be greater than zero" % n
        unit = (ln.get("unit") or item["unit"] or "each").strip()
        clean.append({"item_id": item["id"], "qty_per_batch": qty,
                      "unit": unit, "notes": (ln.get("notes") or "").strip()})
    if not clean:
        return None, "at least one recipe line is required"
    return clean, None


def _erp_batch_shortfalls(conn, lines, planned_qty, batch_size, location_id):
    """Check ingredient availability for a planned batch.

    Returns [(sku, item_name, unit, required, on_hand), ...] for shortfalls.
    """
    short = []
    if batch_size <= 0:
        return short
    scale = float(planned_qty) / float(batch_size)
    for ln in lines:
        required = float(ln["qty_per_batch"]) * scale
        on_hand = _erp_on_hand(conn, ln["item_id"], location_id)
        if on_hand + 1e-9 < required:
            item = _erp_get_item(conn, ln["item_id"])
            short.append({"item_id": ln["item_id"], "sku": item["sku"],
                          "item_name": item["name"], "unit": ln["unit"],
                          "required": required, "on_hand": on_hand})
    return short


@app.get("/api/erp/recipes")
def erp_list_recipes():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    rows = conn.execute(
        "SELECT r.*, (SELECT COUNT(*) FROM erp_recipe_lines rl"
        " WHERE rl.recipe_id = r.id AND rl.recipe_version = r.version) AS line_count,"
        " (SELECT COUNT(DISTINCT recipe_version) FROM erp_recipe_lines rl"
        " WHERE rl.recipe_id = r.id) AS versions"
        " FROM erp_recipes r WHERE r.active = 1 ORDER BY r.name").fetchall()
    conn.close()
    return jsonify(recipes=[dict(r) for r in rows])


@app.post("/api/erp/recipes")
def erp_create_recipe():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()
    if not name:
        return jsonify(error="name is required"), 400
    try:
        batch_size = float(data.get("batch_size_bags") or 0)
    except (TypeError, ValueError):
        return jsonify(error="batch_size_bags must be a number"), 400
    if batch_size <= 0:
        return jsonify(error="batch_size_bags must be greater than zero"), 400
    conn = db()
    clean, err_msg = _erp_validate_recipe_lines(conn, data.get("lines"))
    if err_msg:
        conn.close()
        return jsonify(error=err_msg), 400
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_recipes (name, batch_size_bags, version, active, notes,"
        " created_by, created_at) VALUES (?, ?, 1, 1, ?, ?, ?)",
        (name, batch_size, (data.get("notes") or "").strip(), actor, now))
    recipe_id = cur.lastrowid
    for ln in clean:
        conn.execute(
            "INSERT INTO erp_recipe_lines (recipe_id, recipe_version, item_id,"
            " qty_per_batch, unit, notes) VALUES (?, 1, ?, ?, ?, ?)",
            (recipe_id, ln["item_id"], ln["qty_per_batch"], ln["unit"],
             ln["notes"]))
    conn.commit()
    row = conn.execute("SELECT * FROM erp_recipes WHERE id = ?",
                       (recipe_id,)).fetchone()
    lines = _erp_recipe_lines(conn, recipe_id, 1)
    conn.close()
    return jsonify(recipe=dict(row), lines=[dict(l) for l in lines]), 201


@app.get("/api/erp/recipes/<int:recipe_id>")
def erp_get_recipe(recipe_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    recipe = _erp_get_recipe(conn, recipe_id)
    if not recipe or not recipe["active"]:
        conn.close()
        return jsonify(error="recipe not found"), 404
    version = request.args.get("version")
    try:
        version = int(version) if version else recipe["version"]
    except (TypeError, ValueError):
        version = recipe["version"]
    lines = _erp_recipe_lines(conn, recipe_id, version)
    versions = [r["recipe_version"] for r in conn.execute(
        "SELECT DISTINCT recipe_version FROM erp_recipe_lines"
        " WHERE recipe_id = ? ORDER BY recipe_version", (recipe_id,)).fetchall()]
    conn.close()
    return jsonify(recipe=dict(recipe), version=version,
                   lines=[dict(l) for l in lines], versions=versions)


@app.put("/api/erp/recipes/<int:recipe_id>")
def erp_update_recipe(recipe_id):
    """Edit a recipe by creating a new version. Old batches keep the old version."""
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    recipe = _erp_get_recipe(conn, recipe_id)
    if not recipe or not recipe["active"]:
        conn.close()
        return jsonify(error="recipe not found"), 404
    new_version = int(recipe["version"]) + 1
    name = (data.get("name") or "").strip() or recipe["name"]
    try:
        batch_size = float(data.get("batch_size_bags") or recipe["batch_size_bags"])
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="batch_size_bags must be a number"), 400
    if batch_size <= 0:
        conn.close()
        return jsonify(error="batch_size_bags must be greater than zero"), 400
    if "lines" in data:
        clean, err_msg = _erp_validate_recipe_lines(conn, data.get("lines"))
        if err_msg:
            conn.close()
            return jsonify(error=err_msg), 400
    else:
        old_lines = _erp_recipe_lines(conn, recipe_id, recipe["version"])
        clean = [{"item_id": l["item_id"], "qty_per_batch": float(l["qty_per_batch"]),
                  "unit": l["unit"], "notes": l["notes"]} for l in old_lines]
    notes = data.get("notes")
    notes = recipe["notes"] if notes is None else (notes or "").strip()
    conn.execute(
        "UPDATE erp_recipes SET name = ?, batch_size_bags = ?, version = ?,"
        " notes = ? WHERE id = ?",
        (name, batch_size, new_version, notes, recipe_id))
    for ln in clean:
        conn.execute(
            "INSERT INTO erp_recipe_lines (recipe_id, recipe_version, item_id,"
            " qty_per_batch, unit, notes) VALUES (?, ?, ?, ?, ?, ?)",
            (recipe_id, new_version, ln["item_id"], ln["qty_per_batch"],
             ln["unit"], ln["notes"]))
    conn.commit()
    row = conn.execute("SELECT * FROM erp_recipes WHERE id = ?",
                       (recipe_id,)).fetchone()
    lines = _erp_recipe_lines(conn, recipe_id, new_version)
    conn.close()
    return jsonify(recipe=dict(row), lines=[dict(l) for l in lines])


@app.post("/api/erp/recipes/import")
def erp_import_recipes():
    """CSV import of recipes. Columns: recipe_name, batch_size_bags, sku,
    qty_per_batch, unit, notes. One row per recipe line; rows sharing a
    recipe_name belong to the same recipe (first batch_size_bags wins)."""
    import csv
    import io
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    text = data.get("csv") or ""
    if not text.strip():
        return jsonify(error="csv text is required"), 400
    conn = db()
    reader = csv.DictReader(io.StringIO(text))
    grouped = {}
    order = []
    for n, row in enumerate(reader, 2):
        row = { (k or "").strip(): (v or "").strip() for k, v in row.items() }
        rname = row.get("recipe_name") or ""
        if not rname:
            conn.close()
            return jsonify(error="row %d: recipe_name is required" % n), 400
        try:
            batch_size = float(row.get("batch_size_bags") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="row %d: batch_size_bags must be a number" % n), 400
        if batch_size <= 0:
            conn.close()
            return jsonify(error="row %d: batch_size_bags must be > 0" % n), 400
        item = conn.execute("SELECT * FROM erp_items WHERE sku = ?",
                            (row.get("sku") or "",)).fetchone()
        if not item or not item["active"]:
            conn.close()
            return jsonify(error="row %d: unknown sku '%s'" % (n, row.get("sku"))), 400
        try:
            qty = float(row.get("qty_per_batch") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="row %d: qty_per_batch must be a number" % n), 400
        if qty <= 0:
            conn.close()
            return jsonify(error="row %d: qty_per_batch must be > 0" % n), 400
        if rname not in grouped:
            grouped[rname] = {"batch_size_bags": batch_size,
                              "notes": row.get("notes") or "", "lines": []}
            order.append(rname)
        grouped[rname]["lines"].append({
            "item_id": item["id"], "qty_per_batch": qty,
            "unit": row.get("unit") or item["unit"] or "each", "notes": ""})
    if not grouped:
        conn.close()
        return jsonify(error="no recipe rows found"), 400
    now = datetime.now(timezone.utc).isoformat()
    created = 0
    for rname in order:
        g = grouped[rname]
        clean, err_msg = _erp_validate_recipe_lines(conn, g["lines"])
        if err_msg:
            conn.close()
            return jsonify(error="recipe '%s': %s" % (rname, err_msg)), 400
        cur = conn.execute(
            "INSERT INTO erp_recipes (name, batch_size_bags, version, active,"
            " notes, created_by, created_at) VALUES (?, ?, 1, 1, ?, ?, ?)",
            (rname, g["batch_size_bags"], g["notes"], actor, now))
        rid = cur.lastrowid
        for ln in clean:
            conn.execute(
                "INSERT INTO erp_recipe_lines (recipe_id, recipe_version, item_id,"
                " qty_per_batch, unit, notes) VALUES (?, 1, ?, ?, ?, ?)",
                (rid, ln["item_id"], ln["qty_per_batch"], ln["unit"], ln["notes"]))
        created += 1
    conn.commit()
    conn.close()
    return jsonify(ok=True, imported=created)


def _erp_batch_dict(conn, batch):
    d = dict(batch)
    recipe = _erp_get_recipe(conn, batch["recipe_id"])
    d["recipe_name"] = recipe["name"] if recipe else ""
    loc = _erp_get_location(conn, batch["location_id"])
    d["location_code"] = loc["code"] if loc else ""
    if batch["total_cost_cents"] and batch["actual_qty_bags"]:
        d["cost_per_bag_cents"] = int(round(
            float(batch["total_cost_cents"]) / float(batch["actual_qty_bags"])))
    else:
        d["cost_per_bag_cents"] = None
    return d


@app.get("/api/erp/batches")
def erp_list_batches():
    actor, err = _require_erp()
    if err:
        return err
    status = (request.args.get("status") or "").strip()
    conn = db()
    if status and status in ERP_BATCH_STATUSES:
        rows = conn.execute(
            "SELECT * FROM erp_production_batches WHERE status = ?"
            " ORDER BY id DESC", (status,)).fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM erp_production_batches ORDER BY id DESC").fetchall()
    out = [_erp_batch_dict(conn, b) for b in rows]
    conn.close()
    return jsonify(batches=out)


@app.post("/api/erp/batches")
def erp_create_batch():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    recipe = _erp_get_recipe(conn, data.get("recipe_id"))
    if not recipe or not recipe["active"]:
        conn.close()
        return jsonify(error="valid recipe_id is required"), 400
    try:
        planned = float(data.get("planned_qty_bags") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="planned_qty_bags must be a number"), 400
    if planned <= 0:
        conn.close()
        return jsonify(error="planned_qty_bags must be greater than zero"), 400
    loc = _erp_get_location(conn, data.get("location_id"))
    if not loc:
        loc = _erp_get_location_by_code(conn, "HEND")
    if not loc or not loc["active"]:
        conn.close()
        return jsonify(error="valid location_id is required"), 400
    lines = _erp_recipe_lines(conn, recipe["id"], recipe["version"])
    if not lines:
        conn.close()
        return jsonify(error="recipe has no lines"), 400
    shortfalls = _erp_batch_shortfalls(
        conn, [{"item_id": l["item_id"], "qty_per_batch": float(l["qty_per_batch"]),
                "unit": l["unit"]} for l in lines],
        planned, float(recipe["batch_size_bags"]), loc["id"])
    count = conn.execute("SELECT COUNT(*) AS c FROM erp_production_batches").fetchone()["c"]
    batch_number = "B-%d" % (1001 + int(count))
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_production_batches (batch_number, recipe_id, recipe_version,"
        " planned_qty_bags, status, location_id, order_ref, produced_by, notes,"
        " created_at) VALUES (?, ?, ?, ?, 'planned', ?, ?, ?, ?, ?)",
        (batch_number, recipe["id"], recipe["version"], planned, loc["id"],
         (data.get("order_ref") or "").strip(), actor,
         (data.get("notes") or "").strip(), now))
    batch_id = cur.lastrowid
    conn.commit()
    batch = conn.execute("SELECT * FROM erp_production_batches WHERE id = ?",
                         (batch_id,)).fetchone()
    out = _erp_batch_dict(conn, batch)
    out["shortfalls"] = shortfalls
    conn.close()
    return jsonify(batch=out), 201


@app.get("/api/erp/batches/<int:batch_id>")
def erp_get_batch(batch_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    lines = _erp_recipe_lines(conn, batch["recipe_id"], batch["recipe_version"])
    scale = 0
    if float(batch["recipe_id"] or 0):
        recipe = _erp_get_recipe(conn, batch["recipe_id"])
        bs = float(recipe["batch_size_bags"]) if recipe else 0
        base_qty = float(batch["actual_qty_bags"] or batch["planned_qty_bags"])
        scale = (base_qty / bs) if bs > 0 else 0
    scaled = []
    for l in lines:
        d = dict(l)
        d["qty_for_batch"] = float(l["qty_per_batch"]) * scale
        d["on_hand"] = _erp_on_hand(conn, l["item_id"], batch["location_id"])
        scaled.append(d)
    used = [dict(r) for r in conn.execute(
        "SELECT bi.*, i.sku, i.name AS item_name FROM erp_batch_ingredients bi"
        " JOIN erp_items i ON i.id = bi.item_id"
        " WHERE bi.batch_id = ? ORDER BY bi.id", (batch_id,)).fetchall()]
    out = _erp_batch_dict(conn, batch)
    conn.close()
    out["recipe_lines"] = scaled
    out["ingredients_used"] = used
    return jsonify(batch=out)


@app.post("/api/erp/batches/<int:batch_id>/start")
def erp_batch_start(batch_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    if batch["status"] != "planned":
        conn.close()
        return jsonify(error="only planned batches can be started"), 400
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        "UPDATE erp_production_batches SET status = 'in_progress', started_at = ?,"
        " produced_by = ? WHERE id = ?", (now, actor, batch_id))
    conn.commit()
    conn.close()
    return jsonify(ok=True, batch_id=batch_id, status="in_progress")


@app.post("/api/erp/batches/<int:batch_id>/complete")
def erp_batch_complete(batch_id):
    """Complete a batch: consume ingredients (FIFO lots) via production_out
    movements, snapshot costs, stamp lot code + 6-month expiry. All-or-nothing."""
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    if batch["status"] != "in_progress":
        conn.close()
        return jsonify(error="only in-progress batches can be completed"), 400
    try:
        actual = float(data.get("actual_qty_bags") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="actual_qty_bags must be a number"), 400
    if actual <= 0:
        conn.close()
        return jsonify(error="actual_qty_bags must be greater than zero"), 400
    try:
        waste = float(data.get("waste_qty_bags") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="waste_qty_bags must be a number"), 400
    if waste < 0:
        conn.close()
        return jsonify(error="waste_qty_bags cannot be negative"), 400
    recipe = _erp_get_recipe(conn, batch["recipe_id"])
    batch_size = float(recipe["batch_size_bags"]) if recipe else 0
    if batch_size <= 0:
        conn.close()
        return jsonify(error="recipe has invalid batch size"), 400
    lines = _erp_recipe_lines(conn, batch["recipe_id"], batch["recipe_version"])
    if not lines:
        conn.close()
        return jsonify(error="recipe has no lines"), 400
    # Validate stock for everything BEFORE writing (all-or-nothing).
    scale = actual / batch_size
    plan = []
    for l in lines:
        need = float(l["qty_per_batch"]) * scale
        on_hand = _erp_on_hand(conn, l["item_id"], batch["location_id"])
        if on_hand + 1e-9 < need:
            conn.close()
            return jsonify(error="insufficient stock of %s (have %s %s, need %s %s)"
                           % (l["sku"], _erp_fmt_qty(on_hand), l["unit"],
                              _erp_fmt_qty(need), l["unit"])), 400
        plan.append((l, need))
    # Consume FIFO lots, post movements, snapshot costs.
    total_cost = 0
    today = datetime.now(timezone.utc).date()
    today_s = today.isoformat()
    lot_code = "%s-%s" % (today_s.replace("-", ""), batch["batch_number"])
    expiry = _erp_expiry_plus_months(today_s, 6)
    for l, need in plan:
        item = _erp_get_item(conn, l["item_id"])
        avg = int(item["avg_cost_cents"] or 0)
        remaining = need
        if item["track_lots"]:
            for lcode, lqty, _ in _erp_lot_balances(conn, item["id"],
                                                    batch["location_id"]):
                if remaining <= 1e-9:
                    break
                take = min(lqty, remaining)
                _erp_post_movement(conn, item["id"], batch["location_id"], -take,
                                   "production_out", actor, ref_type="batch",
                                   ref_id=batch["batch_number"], lot_code=lcode,
                                   unit_cost_cents=avg,
                                   note="Batch %s" % batch["batch_number"])
                conn.execute(
                    "INSERT INTO erp_batch_ingredients (batch_id, item_id, lot_code,"
                    " qty_used, unit, unit_cost_cents) VALUES (?, ?, ?, ?, ?, ?)",
                    (batch_id, item["id"], lcode, take, l["unit"], avg))
                total_cost += take * avg
                remaining -= take
        if remaining > 1e-9:
            _erp_post_movement(conn, item["id"], batch["location_id"], -remaining,
                               "production_out", actor, ref_type="batch",
                               ref_id=batch["batch_number"], lot_code="",
                               unit_cost_cents=avg,
                               note="Batch %s" % batch["batch_number"])
            conn.execute(
                "INSERT INTO erp_batch_ingredients (batch_id, item_id, lot_code,"
                " qty_used, unit, unit_cost_cents) VALUES (?, ?, '', ?, ?, ?)",
                (batch_id, item["id"], remaining, l["unit"], avg))
            total_cost += remaining * avg
    total_cost_cents = int(round(total_cost))
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        "UPDATE erp_production_batches SET status = 'completed',"
        " actual_qty_bags = ?, waste_qty_bags = ?, lot_code = ?, expiry_date = ?,"
        " total_cost_cents = ?, completed_at = ?, produced_by = ? WHERE id = ?",
        (actual, waste, lot_code, expiry, total_cost_cents, now, actor, batch_id))
    conn.commit()
    batch = conn.execute("SELECT * FROM erp_production_batches WHERE id = ?",
                         (batch_id,)).fetchone()
    out = _erp_batch_dict(conn, batch)
    conn.close()
    return jsonify(batch=out)


@app.post("/api/erp/batches/<int:batch_id>/cancel")
def erp_batch_cancel(batch_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    if batch["status"] not in ("planned", "in_progress"):
        conn.close()
        return jsonify(error="only planned or in-progress batches can be cancelled"), 400
    conn.execute("UPDATE erp_production_batches SET status = 'cancelled' WHERE id = ?",
                 (batch_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True, batch_id=batch_id, status="cancelled")


@app.post("/api/erp/batches/<int:batch_id>/reverse")
def erp_batch_reverse(batch_id):
    """Reverse a completed batch: post compensating production_reversal movements
    (stock back in) and mark the batch reversed. Never edits history."""
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    if batch["status"] != "completed":
        conn.close()
        return jsonify(error="only completed batches can be reversed"), 400
    used = conn.execute(
        "SELECT * FROM erp_batch_ingredients WHERE batch_id = ?",
        (batch_id,)).fetchall()
    for u in used:
        _erp_post_movement(conn, u["item_id"], batch["location_id"],
                           float(u["qty_used"]), "production_reversal", actor,
                           ref_type="batch", ref_id=batch["batch_number"],
                           lot_code=u["lot_code"],
                           unit_cost_cents=int(u["unit_cost_cents"] or 0),
                           note="Reversal of batch %s" % batch["batch_number"])
    conn.execute("UPDATE erp_production_batches SET status = 'reversed' WHERE id = ?",
                 (batch_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True, batch_id=batch_id, status="reversed")


@app.get("/api/erp/batches/<int:batch_id>/trace")
def erp_batch_trace(batch_id):
    """Lot traceability: finished lot -> ingredient lots used."""
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    used = [dict(r) for r in conn.execute(
        "SELECT bi.*, i.sku, i.name AS item_name FROM erp_batch_ingredients bi"
        " JOIN erp_items i ON i.id = bi.item_id"
        " WHERE bi.batch_id = ? ORDER BY bi.id", (batch_id,)).fetchall()]
    conn.close()
    return jsonify(batch_number=batch["batch_number"], lot_code=batch["lot_code"],
                   expiry_date=batch["expiry_date"], status=batch["status"],
                   ingredients=used)


# ---------------- ERP Phase 3: Order hub + wholesale CRM ----------------

_ERP_FULFILLMENT_STATUSES = ("new", "submitted", "accepted", "in_production", "ready", "shipped",
                             "picked_up", "cancelled")
_ERP_ORDER_SOURCES = ("stripe", "paypal", "wholesale")


def _erp_get_fulfillment(conn, source, order_id):
    return conn.execute(
        "SELECT * FROM erp_order_fulfillment WHERE order_source = ? AND order_id = ?",
        (source, order_id)).fetchone()


def _erp_set_fulfillment(conn, source, order_id, status, actor, note=""):
    """Write fulfillment status (side table + history). For wholesale also
    mirrors onto erp_wholesale_orders.status so the order row stays truthful."""
    if status not in _ERP_FULFILLMENT_STATUSES:
        return "unknown status '%s'" % status
    now = datetime.now(timezone.utc).isoformat()
    existing = _erp_get_fulfillment(conn, source, order_id)
    if existing:
        conn.execute(
            "UPDATE erp_order_fulfillment SET status = ?, updated_by = ?,"
            " updated_at = ?, note = ? WHERE id = ?",
            (status, actor, now, note or "", existing["id"]))
    else:
        conn.execute(
            "INSERT INTO erp_order_fulfillment (order_source, order_id, status,"
            " updated_by, updated_at, note) VALUES (?, ?, ?, ?, ?, ?)",
            (source, order_id, status, actor, now, note or ""))
    conn.execute(
        "INSERT INTO erp_fulfillment_history (order_source, order_id, status,"
        " updated_by, updated_at, note) VALUES (?, ?, ?, ?, ?, ?)",
        (source, order_id, status, actor, now, note or ""))
    if source == "wholesale":
        conn.execute("UPDATE erp_wholesale_orders SET status = ? WHERE id = ?",
                     (status, order_id))
    return None


def _erp_ensure_production_lines(conn, order_id):
    """Generate per-flavor production checklist lines from the order's lines.
    Idempotent: does nothing if lines already exist for the order."""
    existing = conn.execute(
        "SELECT COUNT(*) AS c FROM erp_order_production_lines WHERE order_id = ?",
        (order_id,)).fetchone()["c"]
    if existing:
        return
    for li in conn.execute(
            "SELECT flavor_name, qty_bags FROM erp_wholesale_order_lines"
            " WHERE order_id = ? ORDER BY id", (order_id,)).fetchall():
        conn.execute(
            "INSERT INTO erp_order_production_lines (order_id, flavor_name, qty_bags,"
            " done, done_by, done_at) VALUES (?, ?, ?, 0, '', '')",
            (order_id, li["flavor_name"], li["qty_bags"]))


def _erp_production_progress(conn, order_id):
    rows = conn.execute(
        "SELECT COUNT(*) AS n, COALESCE(SUM(done), 0) AS d"
        " FROM erp_order_production_lines WHERE order_id = ?",
        (order_id,)).fetchone()
    return int(rows["d"] or 0), int(rows["n"] or 0)


def _erp_fulfillment_dict(conn, source, order_id):
    row = _erp_get_fulfillment(conn, source, order_id)
    status = row["status"] if row else "new"
    hist = [dict(h) for h in conn.execute(
        "SELECT status, updated_by, updated_at, note FROM erp_fulfillment_history"
        " WHERE order_source = ? AND order_id = ? ORDER BY id",
        (source, order_id)).fetchall()]
    return {"status": status, "history": hist}


def _erp_online_order(conn, source, order_id):
    """Read-only view of a checkout order. Returns dict or None."""
    if source == "stripe":
        r = conn.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not r:
            return None
        return {"source": "stripe", "id": r["id"],
                "number": "#%d" % (1000 + r["id"]),
                "customer_name": r["customer_name"] or "",
                "email": r["email"] or "",
                "shipping_address": r["shipping_address"] or "",
                "items_summary": r["items_summary"] or "",
                "total_cents": r["amount_total_cents"] or 0,
                "total_qty": r["total_qty"] or 0,
                "tracking_number": r["shippo_tracking_number"] or "",
                "created_at": r["created_at"]}
    if source == "paypal":
        r = conn.execute("SELECT * FROM paypal_orders WHERE id = ?",
                         (order_id,)).fetchone()
        if not r:
            return None
        return {"source": "paypal", "id": r["id"],
                "number": "#%d" % (1000 + r["id"]),
                "customer_name": "",
                "email": r["email"] or "",
                "shipping_address": "",
                "items_summary": r["items_summary"] or "",
                "total_cents": r["amount_total_cents"] or 0,
                "total_qty": r["total_qty"] or 0,
                "tracking_number": "",
                "created_at": r["created_at"]}
    return None


def _erp_wholesale_account_dict(conn, a):
    n = conn.execute("SELECT COUNT(*) AS c FROM erp_wholesale_orders"
                     " WHERE account_id = ?", (a["id"],)).fetchone()["c"]
    d = dict(a)
    d["order_count"] = n
    return d


def _erp_wholesale_order_totals(conn, order_id):
    rows = conn.execute("SELECT qty_bags, line_total_cents FROM erp_wholesale_order_lines"
                        " WHERE order_id = ?", (order_id,)).fetchall()
    return (sum(float(r["qty_bags"]) for r in rows),
            sum(int(r["line_total_cents"]) for r in rows))


def _erp_wholesale_order_brief(conn, w):
    acct = conn.execute("SELECT name FROM erp_wholesale_accounts WHERE id = ?",
                        (w["account_id"],)).fetchone()
    qty, total = _erp_wholesale_order_totals(conn, w["id"])
    return {"source": "wholesale", "id": w["id"], "number": w["order_number"],
            "order_number": w["order_number"],
            "customer_name": acct["name"] if acct else "",
            "account_name": acct["name"] if acct else "",
            "account_id": w["account_id"],
            "pricing_mode": (w["pricing_mode"] if "pricing_mode" in w.keys() else "") or "bag",
            "email": "", "items_summary": "",
            "total_cents": total, "total_qty": qty,
            "status": w["status"], "created_at": w["created_at"],
            "due_date": w["due_date"], "via_edi": bool(w["via_edi"])}


def _erp_order_brief(conn, source, order_id):
    """Queue/link representation of any order, or None if it doesn't exist."""
    if source in ("stripe", "paypal"):
        o = _erp_online_order(conn, source, order_id)
        if not o:
            return None
        o["due_date"] = ""
        o["via_edi"] = False
        o["account_name"] = ""
        return o
    if source == "wholesale":
        w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                         (order_id,)).fetchone()
        if not w:
            return None
        return _erp_wholesale_order_brief(conn, w)
    return None


def _erp_batch_link_dict(conn, link):
    b = conn.execute("SELECT batch_number, lot_code, status FROM erp_production_batches"
                     " WHERE id = ?", (link["batch_id"],)).fetchone()
    o = _erp_order_brief(conn, link["order_source"], link["order_id"])
    return {"id": link["id"], "link_id": link["id"], "batch_id": link["batch_id"],
            "batch_number": b["batch_number"] if b else "",
            "lot_code": b["lot_code"] if b else "",
            "batch_status": b["status"] if b else "",
            "order_source": link["order_source"], "order_id": link["order_id"],
            "order_number": o["number"] if o else "",
            "customer_name": o["customer_name"] if o else "",
            "qty_bags": link["qty_bags"], "created_by": link["created_by"],
            "created_at": link["created_at"]}


def _erp_order_links(conn, source, order_id):
    links = conn.execute(
        "SELECT * FROM erp_batch_orders WHERE order_source = ? AND order_id = ?"
        " ORDER BY id", (source, order_id)).fetchall()
    return [_erp_batch_link_dict(conn, l) for l in links]


@app.get("/api/erp/orders")
def erp_order_queue():
    """Unified order queue: stripe + paypal (read-only) + wholesale."""
    actor, err = _require_erp()
    if err:
        return err
    source = (request.args.get("source") or "").strip()
    status = (request.args.get("status") or "").strip()
    q = (request.args.get("q") or "").strip().lower()
    if source and source not in _ERP_ORDER_SOURCES:
        return jsonify(error="unknown source"), 400
    if status and status not in _ERP_FULFILLMENT_STATUSES:
        return jsonify(error="unknown status"), 400
    conn = db()
    orders = []
    if not source or source == "stripe":
        for r in conn.execute("SELECT * FROM orders ORDER BY id DESC").fetchall():
            orders.append(_erp_order_brief(conn, "stripe", r["id"]))
    if not source or source == "paypal":
        for r in conn.execute("SELECT * FROM paypal_orders ORDER BY id DESC").fetchall():
            orders.append(_erp_order_brief(conn, "paypal", r["id"]))
    if not source or source == "wholesale":
        for w in conn.execute(
                "SELECT * FROM erp_wholesale_orders ORDER BY id DESC").fetchall():
            orders.append(_erp_wholesale_order_brief(conn, w))
    fulf = {(f["order_source"], f["order_id"]): f["status"]
            for f in conn.execute("SELECT order_source, order_id, status"
                                  " FROM erp_order_fulfillment").fetchall()}
    for o in orders:
        o["status"] = fulf.get((o["source"], o["id"]), "new")
    if status:
        orders = [o for o in orders if o["status"] == status]
    if q:
        orders = [o for o in orders
                  if q in (o["number"] or "").lower()
                  or q in (o["customer_name"] or "").lower()
                  or q in (o["email"] or "").lower()
                  or q in (o["items_summary"] or "").lower()]
    orders.sort(key=lambda o: o["created_at"] or "", reverse=True)
    conn.close()
    return jsonify(orders=orders)


@app.get("/api/erp/orders/<source>/<int:order_id>")
def erp_order_detail(source, order_id):
    actor, err = _require_erp()
    if err:
        return err
    if source not in _ERP_ORDER_SOURCES:
        return jsonify(error="unknown source"), 404
    conn = db()
    if source == "wholesale":
        w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                         (order_id,)).fetchone()
        if not w:
            conn.close()
            return jsonify(error="order not found"), 404
        order = _erp_wholesale_order_brief(conn, w)
        order["lines"] = [dict(l) for l in conn.execute(
            "SELECT * FROM erp_wholesale_order_lines WHERE order_id = ? ORDER BY id",
            (order_id,)).fetchall()]
        acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                            (w["account_id"],)).fetchone()
        order["account"] = dict(acct) if acct else None
        order["notes"] = w["notes"]
        order["order_date"] = w["order_date"]
        order["tracking_number"] = ""
        order["shipping_address"] = acct["address"] if acct else ""
        qb_link = _qb_pushed(conn, "wholesale_order", order_id, "invoice")
        order["qb_invoice_id"] = qb_link["qb_id"] if qb_link else None
    else:
        order = _erp_online_order(conn, source, order_id)
        if not order:
            conn.close()
            return jsonify(error="order not found"), 404
        order["due_date"] = ""
        order["via_edi"] = False
        order["account_name"] = ""
        order["account"] = None
        order["lines"] = None
        order["notes"] = ""
        order["order_date"] = ""
    fulf = _erp_fulfillment_dict(conn, source, order_id)
    order["status"] = fulf["status"]
    order["fulfillment"] = fulf
    order["linked_batches"] = _erp_order_links(conn, source, order_id)
    conn.close()
    return jsonify(order=order)


@app.post("/api/erp/orders/<source>/<int:order_id>/status")
def erp_order_set_status(source, order_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    if source not in _ERP_ORDER_SOURCES:
        return jsonify(error="unknown source"), 404
    data = request.get_json(force=True) or {}
    status = (data.get("status") or "").strip()
    note = (data.get("note") or "").strip()
    conn = db()
    if not _erp_order_brief(conn, source, order_id):
        conn.close()
        return jsonify(error="order not found"), 404
    if source == "wholesale" and status == "ready":
        # Phase 5: an order with a production checklist can't be marked ready
        # until every flavor is done.
        done, total = _erp_production_progress(conn, order_id)
        if total and done < total:
            conn.close()
            return jsonify(error="all %d flavors must be marked done first (%d of %d done)"
                           % (total, done, total)), 400
    err_msg = _erp_set_fulfillment(conn, source, order_id, status, actor, note)
    if err_msg:
        conn.close()
        return jsonify(error=err_msg), 400
    if source == "wholesale" and status == "in_production":
        # Phase 5: entering production generates the per-flavor checklist.
        _erp_ensure_production_lines(conn, order_id)
    conn.commit()
    conn.close()
    return jsonify(ok=True, status=status)


# ---------------- wholesale accounts ----------------

@app.get("/api/erp/wholesale-accounts")
def erp_list_wholesale_accounts():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    rows = conn.execute("SELECT * FROM erp_wholesale_accounts ORDER BY name").fetchall()
    out = [_erp_wholesale_account_dict(conn, r) for r in rows]
    conn.close()
    return jsonify(accounts=out)


@app.post("/api/erp/wholesale-accounts")
def erp_create_wholesale_account():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()
    if not name:
        conn = None
        return jsonify(error="name is required"), 400
    pricing_mode = (data.get("pricing_mode") or "bag").strip().lower()
    if pricing_mode not in ("bag", "case"):
        return jsonify(error="pricing_mode must be 'bag' or 'case'"), 400
    try:
        price = int(data.get("price_per_bag_cents", 400) or 400)
    except (TypeError, ValueError):
        return jsonify(error="price_per_bag_cents must be a number"), 400
    if price <= 0:
        return jsonify(error="price_per_bag_cents must be greater than zero"), 400
    try:
        savory = int(data.get("savory_price_cents", 400) or 400)
        sweet = int(data.get("sweet_price_cents", 400) or 400)
    except (TypeError, ValueError):
        return jsonify(error="savory_price_cents and sweet_price_cents must be numbers"), 400
    if savory <= 0 or sweet <= 0:
        return jsonify(error="category prices must be greater than zero"), 400
    conn = db()
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_wholesale_accounts (name, contact_name, email, phone, address,"
        " price_per_bag_cents, payment_terms, notes, active, created_by, created_at,"
        " contact_person, savory_price_cents, sweet_price_cents, default_po,"
        " pricing_mode, account_status)"
        " VALUES (?, ?, ?, ?, ?, ?, ?, ?, 1, ?, ?, ?, ?, ?, ?, ?, 'active')",
        (name, (data.get("contact_name") or "").strip(),
         (data.get("email") or "").strip(), (data.get("phone") or "").strip(),
         (data.get("address") or "").strip(), price,
         (data.get("payment_terms") or "").strip(),
         (data.get("notes") or "").strip(), actor, now,
         (data.get("contact_person") or "").strip(), savory, sweet,
         (data.get("default_po") or "").strip(), pricing_mode))
    account_id = cur.lastrowid
    # Main delivery location: the customer manages further addresses themselves
    # in the portal; the admin sees the profile read-only.
    loc = {k: (data.get(k) or "").strip() for k in
           ("location_name", "street", "city", "state", "zip",
            "location_contact", "location_email", "location_phone")}
    if loc["street"] or loc["location_name"]:
        conn.execute(
            "INSERT INTO erp_wholesale_addresses (account_id, location_name, street,"
            " city, state, zip, contact_name, contact_email, contact_phone,"
            " active, created_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?)",
            (account_id, loc["location_name"] or "Main location", loc["street"],
             loc["city"], loc["state"], loc["zip"], loc["location_contact"],
             loc["location_email"], loc["location_phone"], now))
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    out = _erp_wholesale_account_dict(conn, acct)
    conn.commit()
    conn.close()
    return jsonify(account=out), 201


@app.get("/api/erp/wholesale-accounts/<int:account_id>")
def erp_get_wholesale_account(account_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    orders = [_erp_wholesale_order_brief(conn, w) for w in conn.execute(
        "SELECT * FROM erp_wholesale_orders WHERE account_id = ? ORDER BY id DESC",
        (account_id,)).fetchall()]
    out = _erp_wholesale_account_dict(conn, acct)
    conn.close()
    return jsonify(account=out, orders=orders)


@app.put("/api/erp/wholesale-accounts/<int:account_id>")
def erp_update_wholesale_account(account_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    fields = {}
    for key in ("name", "contact_name", "email", "phone", "address",
                "payment_terms", "notes", "contact_person", "default_po"):
        if key in data:
            fields[key] = (data.get(key) or "").strip()
    if "price_per_bag_cents" in data:
        try:
            price = int(data.get("price_per_bag_cents") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="price_per_bag_cents must be a number"), 400
        if price <= 0:
            conn.close()
            return jsonify(error="price_per_bag_cents must be greater than zero"), 400
        fields["price_per_bag_cents"] = price
    for key in ("savory_price_cents", "sweet_price_cents"):
        if key in data:
            try:
                price = int(data.get(key) or 0)
            except (TypeError, ValueError):
                conn.close()
                return jsonify(error="%s must be a number" % key), 400
            if price <= 0:
                conn.close()
                return jsonify(error="%s must be greater than zero" % key), 400
            fields[key] = price
    if "account_status" in data:
        st = (data.get("account_status") or "").strip()
        if st not in ("invited", "active", "deactivated"):
            conn.close()
            return jsonify(error="account_status must be invited, active, or deactivated"), 400
        fields["account_status"] = st
    if "pricing_mode" in data:
        pm = (data.get("pricing_mode") or "").strip().lower()
        if pm not in ("bag", "case"):
            conn.close()
            return jsonify(error="pricing_mode must be 'bag' or 'case'"), 400
        fields["pricing_mode"] = pm
    if "active" in data:
        fields["active"] = 1 if data.get("active") else 0
    if "name" in fields and not fields["name"]:
        conn.close()
        return jsonify(error="name is required"), 400
    if fields:
        sets = ", ".join("%s = ?" % k for k in fields)
        conn.execute("UPDATE erp_wholesale_accounts SET %s WHERE id = ?" % sets,
                     tuple(fields.values()) + (account_id,))
        conn.commit()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    out = _erp_wholesale_account_dict(conn, acct)
    conn.close()
    return jsonify(account=out)


@app.post("/api/erp/wholesale-accounts/import")
def erp_import_wholesale_accounts():
    """CSV import. Columns: name, contact_name, email, phone, address,
    price_per_bag_cents, payment_terms, notes. Fail-fast with row numbers,
    same pattern as the recipe import."""
    import csv
    import io
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    text = data.get("csv") or ""
    if not text.strip():
        return jsonify(error="csv text is required"), 400
    conn = db()
    reader = csv.DictReader(io.StringIO(text))
    rows = []
    for n, row in enumerate(reader, 2):
        row = {(k or "").strip(): (v or "").strip() for k, v in row.items()}
        name = row.get("name") or ""
        if not name:
            conn.close()
            return jsonify(error="row %d: name is required" % n), 400
        try:
            price = int(row.get("price_per_bag_cents") or 400)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="row %d: price_per_bag_cents must be a number" % n), 400
        if price <= 0:
            conn.close()
            return jsonify(error="row %d: price_per_bag_cents must be > 0" % n), 400
        rows.append({"name": name, "contact_name": row.get("contact_name") or "",
                     "email": row.get("email") or "", "phone": row.get("phone") or "",
                     "address": row.get("address") or "", "price_per_bag_cents": price,
                     "payment_terms": row.get("payment_terms") or "",
                     "notes": row.get("notes") or ""})
    if not rows:
        conn.close()
        return jsonify(error="no account rows found"), 400
    now = datetime.now(timezone.utc).isoformat()
    for r in rows:
        conn.execute(
            "INSERT INTO erp_wholesale_accounts (name, contact_name, email, phone, address,"
            " price_per_bag_cents, payment_terms, notes, active, created_by, created_at)"
            " VALUES (?, ?, ?, ?, ?, ?, ?, ?, 1, ?, ?)",
            (r["name"], r["contact_name"], r["email"], r["phone"], r["address"],
             r["price_per_bag_cents"], r["payment_terms"], r["notes"], actor, now))
    conn.commit()
    conn.close()
    return jsonify(imported=len(rows))


# ---------------- wholesale orders ----------------

def _erp_next_wholesale_number(conn):
    count = conn.execute("SELECT COUNT(*) AS c FROM erp_wholesale_orders").fetchone()["c"]
    return "W-%d" % (1001 + int(count))


@app.get("/api/erp/wholesale-orders")
def erp_list_wholesale_orders():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    rows = conn.execute("SELECT * FROM erp_wholesale_orders ORDER BY id DESC").fetchall()
    out = [_erp_wholesale_order_brief(conn, w) for w in rows]
    conn.close()
    return jsonify(orders=out)


@app.post("/api/erp/wholesale-orders")
def erp_create_wholesale_order():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (data.get("account_id"),)).fetchone()
    if not acct or not acct["active"]:
        conn.close()
        return jsonify(error="valid account_id is required"), 400
    lines_in = data.get("lines") or []
    if not lines_in:
        conn.close()
        return jsonify(error="at least one order line is required"), 400
    lines = []
    for i, li in enumerate(lines_in, 1):
        flavor = ((li or {}).get("flavor_name") or "").strip()
        if not flavor:
            conn.close()
            return jsonify(error="line %d: flavor_name is required" % i), 400
        try:
            qty = float((li or {}).get("qty_bags") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="line %d: qty_bags must be a number" % i), 400
        if qty <= 0:
            conn.close()
            return jsonify(error="line %d: qty_bags must be greater than zero" % i), 400
        try:
            unit = int((li or {}).get("unit_price_cents") or acct["price_per_bag_cents"])
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="line %d: unit_price_cents must be a number" % i), 400
        if unit <= 0:
            conn.close()
            return jsonify(error="line %d: unit_price_cents must be greater than zero" % i), 400
        lines.append({"flavor_name": flavor, "qty_bags": qty,
                      "unit_price_cents": unit,
                      "line_total_cents": int(round(qty * unit))})
    now = datetime.now(timezone.utc).isoformat()
    order_number = _erp_next_wholesale_number(conn)
    cur = conn.execute(
        "INSERT INTO erp_wholesale_orders (order_number, account_id, status, order_date,"
        " due_date, notes, via_edi, edi_document_id, created_by, created_at)"
        " VALUES (?, ?, 'new', ?, ?, ?, ?, ?, ?, ?)",
        (order_number, acct["id"], (data.get("order_date") or "").strip(),
         (data.get("due_date") or "").strip(), (data.get("notes") or "").strip(),
         1 if data.get("via_edi") else 0, int(data.get("edi_document_id") or 0),
         actor, now))
    order_id = cur.lastrowid
    for li in lines:
        conn.execute(
            "INSERT INTO erp_wholesale_order_lines (order_id, flavor_name, qty_bags,"
            " unit_price_cents, line_total_cents) VALUES (?, ?, ?, ?, ?)",
            (order_id, li["flavor_name"], li["qty_bags"],
             li["unit_price_cents"], li["line_total_cents"]))
    _erp_set_fulfillment(conn, "wholesale", order_id, "new", actor, "order created")
    conn.commit()
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    out = _erp_wholesale_order_brief(conn, w)
    out["lines"] = [dict(l) for l in conn.execute(
        "SELECT * FROM erp_wholesale_order_lines WHERE order_id = ? ORDER BY id",
        (order_id,)).fetchall()]
    conn.close()
    return jsonify(order=out), 201


@app.get("/api/erp/wholesale-orders/<int:order_id>")
def erp_get_wholesale_order(order_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    if not w:
        conn.close()
        return jsonify(error="order not found"), 404
    order = _erp_wholesale_order_brief(conn, w)
    order["lines"] = [dict(l) for l in conn.execute(
        "SELECT * FROM erp_wholesale_order_lines WHERE order_id = ? ORDER BY id",
        (order_id,)).fetchall()]
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (w["account_id"],)).fetchone()
    order["account"] = dict(acct) if acct else None
    order["notes"] = w["notes"]
    order["order_date"] = w["order_date"]
    order["tracking_number"] = ""
    order["shipping_address"] = acct["address"] if acct else ""
    order["email"] = acct["email"] if acct else ""
    fulf = _erp_fulfillment_dict(conn, "wholesale", order_id)
    order["status"] = fulf["status"]
    order["fulfillment"] = fulf
    order["linked_batches"] = _erp_order_links(conn, "wholesale", order_id)
    conn.close()
    return jsonify(order=order)


# ---------------- ERP Phase 5: wholesale customer portal ----------------

_WHOLESALE_ADMIN_EMAILS = ("dj@fudgetopia.net", "matt@fudgetopia.net")


def _wholesale_portal_url(data):
    base = (data.get("portal_url") or "").strip() if isinstance(data, dict) else ""
    if not base:
        base = os.environ.get("WHOLESALE_PORTAL_URL", "").strip()
    if not base:
        base = "https://erp.pop-a-licious.com"
    return base.rstrip("/")


def _wholesale_account_prices(acct):
    return {"savory": int(acct["savory_price_cents"] or 400),
            "sweet": int(acct["sweet_price_cents"] or 400)}


def _wholesale_flavor_price(conn, acct, flavor_name):
    cat = conn.execute("SELECT category FROM erp_flavor_categories WHERE flavor_name = ?",
                       (flavor_name,)).fetchone()
    category = (cat["category"] if cat else "sweet")
    prices = _wholesale_account_prices(acct)
    return prices["savory"] if category == "savory" else prices["sweet"], category


def _send_wholesale_invite_email(to_email, business_name, link):
    return send_email(
        to_email,
        "You're invited to order Pop-A-Licious wholesale",
        "<p>Hi%s,</p>"
        "<p><strong>%s</strong> has set up a wholesale ordering account for you.</p>"
        "<p><a href=\"%s\">Click here to set your password</a> and start ordering. "
        "This link expires in 7 days.</p>"
        "<p>— Pop-A-Licious</p>"
        % (", " + business_name if business_name else "", business_name or "Pop-A-Licious",
           link))


def _send_new_wholesale_order_emails(order_number, acct, lines, total_cents, po_number,
                                     address_label, portal_url=""):
    dollars = lambda c: "$%s" % "{:,.2f}".format(c / 100)
    case_mode = (acct["pricing_mode"] or "bag") == "case"
    def line_text(l):
        if case_mode and l["qty_bags"] % 12 == 0:
            cases = int(l["qty_bags"] // 12)
            return "%d case%s (12 bags each) &times; %s — %s" % (
                cases, "" if cases == 1 else "s", l["flavor_name"],
                dollars(l["line_total_cents"]))
        return "%s &times; %s — %s" % (l["qty_bags"], l["flavor_name"],
                                       dollars(l["line_total_cents"]))
    line_rows = "".join("<li>%s</li>" % line_text(l) for l in lines)
    accept_url = "%s#/login?accept_order=%s" % (portal_url.rstrip("/"), order_number) \
        if portal_url else ""
    accept_btn = ("<p><a href=\"%s\" style=\"display:inline-block;background:#0d7d7d;color:#fff;"
                  "font-weight:800;padding:12px 28px;border-radius:8px;text-decoration:none;\">"
                  "Accept order</a></p>"
                  "<p style=\"font-size:13px;color:#666;\">Tapping Accept order opens the ERP login — "
                  "after you log in, the order is accepted automatically and the customer is notified.</p>"
                  % accept_url) if accept_url else ""
    html = ("<p>New wholesale order <strong>%s</strong> from <strong>%s</strong>"
            " is waiting for review.</p>"
            "<ul>%s</ul>"
            "<p>Total: <strong>%s</strong><br>PO: %s<br>Deliver to: %s</p>"
            "%s"
            "<p>Or log in to the ERP order hub to review it.</p>"
            % (order_number, acct["name"], line_rows, dollars(total_cents),
               po_number or "—", address_label or "—", accept_btn))
    for to_email in _WHOLESALE_ADMIN_EMAILS:
        send_email(to_email,
                   "New wholesale order %s from %s — review to accept"
                   % (order_number, acct["name"]), html)


def _send_order_accepted_email(to_email, order_number, business_name):
    send_email(
        to_email,
        "Your Pop-A-Licious order %s was accepted" % order_number,
        "<p>Hi%s,</p>"
        "<p>Good news — your wholesale order <strong>%s</strong> has been accepted"
        " and is going into production.</p>"
        "<p>We'll let you know when it ships.<br>— Pop-A-Licious</p>"
        % (", " + business_name if business_name else "", order_number))


def _send_order_declined_email(to_email, order_number, business_name, note):
    send_email(
        to_email,
        "Update on your Pop-A-Licious order %s" % order_number,
        "<p>Hi%s,</p>"
        "<p>Your wholesale order <strong>%s</strong> couldn't be accepted%s.</p>"
        "<p>Please contact us if you have questions.<br>— Pop-A-Licious</p>"
        % (", " + business_name if business_name else "", order_number,
           (" — " + note) if note else ""))


@app.post("/api/wholesale/login")
def wholesale_login():
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""
    conn = db()
    user = conn.execute(
        "SELECT wu.*, wa.account_status, wa.active AS account_active, wa.name AS account_name"
        " FROM erp_wholesale_users wu"
        " JOIN erp_wholesale_accounts wa ON wa.id = wu.account_id"
        " WHERE LOWER(wu.email) = ?", (email,)).fetchone()
    if not user or not user["password_hash"] or \
            not check_password_hash(user["password_hash"], password):
        conn.close()
        return jsonify(error="invalid email or password"), 401
    if not user["active"] or not user["account_active"] \
            or user["account_status"] == "deactivated":
        conn.close()
        return jsonify(error="this account is deactivated"), 403
    token = _issue_wholesale_token(user["id"])
    out = {"token": token, "email": user["email"],
           "account_id": user["account_id"], "account_name": user["account_name"]}
    conn.close()
    return jsonify(out)


@app.post("/api/wholesale/set-password")
def wholesale_set_password():
    data = request.get_json(force=True) or {}
    token = (data.get("token") or "").strip()
    password = data.get("password") or ""
    if not token:
        conn = None
        return jsonify(error="invite token is required"), 400
    if len(password) < 8:
        return jsonify(error="password must be at least 8 characters"), 400
    conn = db()
    user = conn.execute("SELECT * FROM erp_wholesale_users WHERE invite_token = ?",
                        (token,)).fetchone()
    if not user:
        conn.close()
        return jsonify(error="invalid invite token"), 400
    if not user["invite_expires_at"] or user["invite_expires_at"] < datetime.now(timezone.utc).isoformat():
        conn.close()
        return jsonify(error="invite token has expired — ask for a new invitation"), 410
    now = datetime.now(timezone.utc).isoformat()
    conn.execute("UPDATE erp_wholesale_users SET password_hash = ?, invite_token = '',"
                 " invite_expires_at = '', active = 1 WHERE id = ?",
                 (generate_password_hash(password), user["id"]))
    conn.execute("UPDATE erp_wholesale_accounts SET account_status = 'active'"
                 " WHERE id = ? AND account_status = 'invited'", (user["account_id"],))
    conn.commit()
    out_token = _issue_wholesale_token(user["id"])
    acct = conn.execute("SELECT name FROM erp_wholesale_accounts WHERE id = ?",
                        (user["account_id"],)).fetchone()
    conn.close()
    return jsonify(token=out_token, email=user["email"],
                   account_id=user["account_id"],
                   account_name=acct["name"] if acct else "")


def _send_wholesale_reset_email(to_email, business_name, link):
    return send_email(
        to_email,
        "Reset your Pop-A-Licious wholesale password",
        "<p>Hi%s,</p>"
        "<p>We got a request to reset the password for your wholesale ordering account%s.</p>"
        "<p><a href=\"%s\">Click here to set a new password</a>. "
        "This link expires in 1 hour. If you didn't ask for this, just ignore this email.</p>"
        "<p>— Pop-A-Licious</p>"
        % (", " + business_name if business_name else "",
           (" (" + business_name + ")") if business_name else "",
           link))


@app.post("/api/wholesale/forgot-password")
def wholesale_forgot_password():
    data = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip().lower()
    # Always return ok — never reveal whether an email is registered.
    if email and EMAIL_RE.match(email):
        conn = db()
        user = conn.execute("SELECT * FROM erp_wholesale_users WHERE email = ? AND active = 1",
                            (email,)).fetchone()
        if user:
            token = secrets.token_urlsafe(32)
            expires = (datetime.now(timezone.utc) + timedelta(hours=1)).isoformat()
            conn.execute("UPDATE erp_wholesale_users SET invite_token = ?,"
                         " invite_expires_at = ? WHERE id = ?",
                         (token, expires, user["id"]))
            conn.commit()
            acct = conn.execute("SELECT name FROM erp_wholesale_accounts WHERE id = ?",
                                (user["account_id"],)).fetchone()
            link = _wholesale_portal_url(data) + "/#/wholesale-setup?token=" + token
            _send_wholesale_reset_email(email, acct["name"] if acct else "", link)
        conn.close()
    return jsonify(ok=True)


def _wholesale_me_dict(conn, user):
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (user["account_id"],)).fetchone()
    addrs = [dict(a) for a in conn.execute(
        "SELECT * FROM erp_wholesale_addresses WHERE account_id = ? AND active = 1"
        " ORDER BY id", (user["account_id"],)).fetchall()]
    return {"email": user["email"], "account_id": user["account_id"],
            "business_name": acct["name"] if acct else "",
            "contact_person": acct["contact_person"] if acct else "",
            "phone": acct["phone"] if acct else "",
            "default_po": acct["default_po"] if acct else "",
            "pricing_mode": (acct["pricing_mode"] if acct else "") or "bag",
            "account_status": acct["account_status"] if acct else "",
            "addresses": addrs}


@app.get("/api/wholesale/me")
def wholesale_me():
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    conn = db()
    out = _wholesale_me_dict(conn, user)
    conn.close()
    return jsonify(out)


@app.get("/api/wholesale/flavors")
def wholesale_flavors():
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (user["account_id"],)).fetchone()
    prices = _wholesale_account_prices(acct)
    flavors = []
    for row in conn.execute("SELECT flavor_name, category FROM erp_flavor_categories"
                            " ORDER BY category, flavor_name").fetchall():
        flavors.append({"flavor_name": row["flavor_name"], "category": row["category"],
                        "price_cents": prices["savory"] if row["category"] == "savory"
                        else prices["sweet"]})
    conn.close()
    return jsonify(flavors=flavors)


def _wholesale_order_detail(conn, user, order_id):
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ? AND account_id = ?",
                     (order_id, user["account_id"])).fetchone()
    if not w:
        return None
    order = _erp_wholesale_order_brief(conn, w)
    order["lines"] = [dict(l) for l in conn.execute(
        "SELECT * FROM erp_wholesale_order_lines WHERE order_id = ? ORDER BY id",
        (order_id,)).fetchall()]
    order["po_number"] = w["po_number"]
    order["notes"] = w["notes"]
    order["order_date"] = w["order_date"]
    fulf = _erp_fulfillment_dict(conn, "wholesale", order_id)
    order["status"] = fulf["status"]
    order["fulfillment"] = fulf
    addr = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?",
                        (w["address_id"],)).fetchone() if w["address_id"] else None
    order["address"] = dict(addr) if addr else None
    done, total = _erp_production_progress(conn, order_id)
    order["production"] = {"done": done, "total": total}
    return order


@app.get("/api/wholesale/orders")
def wholesale_list_orders():
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    conn = db()
    rows = conn.execute("SELECT * FROM erp_wholesale_orders WHERE account_id = ?"
                        " ORDER BY id DESC", (user["account_id"],)).fetchall()
    out = []
    for w in rows:
        b = _erp_wholesale_order_brief(conn, w)
        b["po_number"] = w["po_number"]
        fulf = _erp_fulfillment_dict(conn, "wholesale", w["id"])
        b["status"] = fulf["status"]
        out.append(b)
    conn.close()
    return jsonify(orders=out)


@app.post("/api/wholesale/orders")
def wholesale_create_order():
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    data = request.get_json(force=True) or {}
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (user["account_id"],)).fetchone()
    lines_in = data.get("lines") or []
    if not lines_in:
        conn.close()
        return jsonify(error="at least one order line is required"), 400
    lines = []
    for i, li in enumerate(lines_in, 1):
        flavor = ((li or {}).get("flavor_name") or "").strip()
        if not flavor:
            conn.close()
            return jsonify(error="line %d: flavor_name is required" % i), 400
        try:
            qty = float((li or {}).get("qty_bags") or 0)
        except (TypeError, ValueError):
            conn.close()
            return jsonify(error="line %d: qty_bags must be a number" % i), 400
        if qty <= 0:
            conn.close()
            return jsonify(error="line %d: qty_bags must be greater than zero" % i), 400
        unit, _cat = _wholesale_flavor_price(conn, acct, flavor)
        if not conn.execute("SELECT 1 FROM erp_flavor_categories WHERE flavor_name = ?",
                            (flavor,)).fetchone():
            conn.close()
            return jsonify(error="line %d: unknown flavor '%s'" % (i, flavor)), 400
        lines.append({"flavor_name": flavor, "qty_bags": qty,
                      "unit_price_cents": unit,
                      "line_total_cents": int(round(qty * unit))})
    # Delivery location: explicit pick, or the single address, or the account address.
    address_id = int(data.get("address_id") or 0)
    addrs = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE account_id = ?"
                         " AND active = 1 ORDER BY id", (acct["id"],)).fetchall()
    if address_id:
        if not any(a["id"] == address_id for a in addrs):
            conn.close()
            return jsonify(error="unknown delivery address"), 400
    elif len(addrs) == 1:
        address_id = addrs[0]["id"]
    elif len(addrs) > 1:
        conn.close()
        return jsonify(error="please choose a delivery location"), 400
    po_number = (data.get("po_number") or "").strip() or (acct["default_po"] or "")
    now = datetime.now(timezone.utc).isoformat()
    order_number = _erp_next_wholesale_number(conn)
    cur = conn.execute(
        "INSERT INTO erp_wholesale_orders (order_number, account_id, status, order_date,"
        " notes, created_by, created_at, po_number, address_id, pricing_mode,"
        " placed_by_user_id)"
        " VALUES (?, ?, 'submitted', ?, ?, ?, ?, ?, ?, ?, ?)",
        (order_number, acct["id"], now[:10], (data.get("notes") or "").strip(),
         "customer:" + user["email"], now, po_number, address_id,
         (acct["pricing_mode"] or "bag"), user["id"]))
    order_id = cur.lastrowid
    for li in lines:
        conn.execute(
            "INSERT INTO erp_wholesale_order_lines (order_id, flavor_name, qty_bags,"
            " unit_price_cents, line_total_cents) VALUES (?, ?, ?, ?, ?)",
            (order_id, li["flavor_name"], li["qty_bags"],
             li["unit_price_cents"], li["line_total_cents"]))
    _erp_set_fulfillment(conn, "wholesale", order_id, "submitted",
                         "customer:" + user["email"], "order placed via customer portal")
    total_cents = sum(li["line_total_cents"] for li in lines)
    addr_label = ""
    if address_id:
        a = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?",
                         (address_id,)).fetchone()
        if a:
            addr_label = "%s — %s, %s %s %s" % (a["label"] or "Delivery",
                                               a["street"], a["city"], a["state"], a["zip"])
    conn.commit()
    order = _wholesale_order_detail(conn, user, order_id)
    conn.close()
    _send_new_wholesale_order_emails(order_number, acct, lines, total_cents,
                                     po_number, addr_label,
                                     _wholesale_portal_url(data))
    return jsonify(order=order), 201


@app.get("/api/wholesale/orders/<int:order_id>")
def wholesale_get_order(order_id):
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    conn = db()
    order = _wholesale_order_detail(conn, user, order_id)
    conn.close()
    if not order:
        return jsonify(error="order not found"), 404
    return jsonify(order=order)


@app.post("/api/wholesale/addresses")
def wholesale_add_address():
    # The customer manages their own delivery locations in their profile.
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    data = request.get_json(force=True) or {}
    location_name = (data.get("location_name") or "").strip()
    street = (data.get("street") or "").strip()
    city = (data.get("city") or "").strip()
    state = (data.get("state") or "").strip()
    zipc = (data.get("zip") or "").strip()
    missing = [f for f, v in (("location name", location_name), ("street", street),
                              ("city", city), ("state", state), ("zip", zipc)) if not v]
    if missing:
        return jsonify(error="missing: " + ", ".join(missing)), 400
    conn = db()
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_wholesale_addresses (account_id, location_name, street,"
        " city, state, zip, contact_name, contact_email, contact_phone,"
        " active, created_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?)",
        (user["account_id"], location_name, street, city, state, zipc,
         (data.get("contact_name") or "").strip(),
         (data.get("contact_email") or "").strip(),
         (data.get("contact_phone") or "").strip(), now))
    addr = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?",
                        (cur.lastrowid,)).fetchone()
    conn.commit()
    conn.close()
    return jsonify(address=dict(addr)), 201


@app.delete("/api/wholesale/addresses/<int:addr_id>")
def wholesale_delete_address(addr_id):
    who, err = _require_wholesale()
    if err:
        return err
    user, _acct = who
    conn = db()
    addr = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?"
                        " AND account_id = ?", (addr_id, user["account_id"])).fetchone()
    if not addr:
        conn.close()
        return jsonify(error="address not found"), 404
    conn.execute("UPDATE erp_wholesale_addresses SET active = 0 WHERE id = ?", (addr_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)


@app.get("/api/erp/wholesale-orders/by-number/<order_number>")
def erp_wholesale_order_by_number(order_number):
    # Powers the "Accept order" button in the new-order admin email: resolves
    # an order number (e.g. W-1002) to its id after the admin logs in.
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    w = conn.execute("SELECT id, order_number, status FROM erp_wholesale_orders"
                     " WHERE order_number = ?", (order_number.strip(),)).fetchone()
    conn.close()
    if not w:
        return jsonify(error="order not found"), 404
    return jsonify(order={"id": w["id"], "order_number": w["order_number"],
                          "status": w["status"]})


@app.post("/api/erp/wholesale-accounts/<int:account_id>/invite")
def erp_invite_wholesale_customer(account_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    if acct["account_status"] == "deactivated" or not acct["active"]:
        conn.close()
        return jsonify(error="account is deactivated"), 400
    email = (acct["email"] or "").strip().lower()
    if not email or not EMAIL_RE.match(email):
        conn.close()
        return jsonify(error="account needs a valid email before inviting"), 400
    token = secrets.token_urlsafe(32)
    expires = (datetime.now(timezone.utc) + timedelta(days=7)).isoformat()
    now = datetime.now(timezone.utc).isoformat()
    existing = conn.execute("SELECT * FROM erp_wholesale_users WHERE email = ?",
                            (email,)).fetchone()
    if existing:
        if existing["account_id"] != account_id:
            conn.close()
            return jsonify(error="that email is already a portal login for another account"), 400
        conn.execute("UPDATE erp_wholesale_users SET invite_token = ?,"
                     " invite_expires_at = ?, active = 1 WHERE id = ?",
                     (token, expires, existing["id"]))
    else:
        conn.execute("INSERT INTO erp_wholesale_users (account_id, email, password_hash,"
                     " invite_token, invite_expires_at, active, created_at)"
                     " VALUES (?, ?, '', ?, ?, 1, ?)",
                     (account_id, email, token, expires, now))
        # First invite for this account: mark it invited (re-invites of active
        # customers leave the status alone).
        conn.execute("UPDATE erp_wholesale_accounts SET account_status = 'invited'"
                     " WHERE id = ? AND account_status = 'active'", (account_id,))
    conn.commit()
    link = _wholesale_portal_url(data) + "/#/wholesale-setup?token=" + token
    conn.close()
    _send_wholesale_invite_email(email, acct["name"], link)
    out = {"ok": True, "email": email}
    if str(request.args.get("reveal") or "") == "1":
        out["invite_link"] = link
    return jsonify(out)


@app.post("/api/erp/wholesale-accounts/<int:account_id>/deactivate")
def erp_deactivate_wholesale_account(account_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    conn.execute("UPDATE erp_wholesale_accounts SET account_status = 'deactivated'"
                 " WHERE id = ?", (account_id,))
    conn.execute("UPDATE erp_wholesale_users SET active = 0 WHERE account_id = ?",
                 (account_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True, account_status="deactivated")


@app.post("/api/erp/wholesale-accounts/<int:account_id>/reactivate")
def erp_reactivate_wholesale_account(account_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    conn.execute("UPDATE erp_wholesale_accounts SET account_status = 'active'"
                 " WHERE id = ?", (account_id,))
    conn.execute("UPDATE erp_wholesale_users SET active = 1 WHERE account_id = ?",
                 (account_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True, account_status="active")


@app.delete("/api/erp/wholesale-accounts/<int:account_id>")
def erp_delete_wholesale_account(account_id):
    # Admin-only full removal: the account, its portal users, addresses,
    # orders and everything attached to those orders (lines, fulfillment
    # history, production checklists, batch links).
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    order_ids = [r["id"] for r in conn.execute(
        "SELECT id FROM erp_wholesale_orders WHERE account_id = ?", (account_id,))]
    if order_ids:
        ph = ",".join("?" * len(order_ids))
        conn.execute("DELETE FROM erp_batch_orders WHERE order_source = 'wholesale'"
                     " AND order_id IN (%s)" % ph, order_ids)
        conn.execute("DELETE FROM erp_order_production_lines WHERE order_id IN (%s)" % ph,
                     order_ids)
        conn.execute("DELETE FROM erp_order_fulfillment WHERE order_source = 'wholesale'"
                     " AND order_id IN (%s)" % ph, order_ids)
        conn.execute("DELETE FROM erp_fulfillment_history WHERE order_source = 'wholesale'"
                     " AND order_id IN (%s)" % ph, order_ids)
        conn.execute("DELETE FROM erp_wholesale_order_lines WHERE order_id IN (%s)" % ph,
                     order_ids)
        conn.execute("DELETE FROM erp_wholesale_orders WHERE account_id = ?", (account_id,))
    conn.execute("DELETE FROM erp_wholesale_users WHERE account_id = ?", (account_id,))
    conn.execute("DELETE FROM erp_wholesale_addresses WHERE account_id = ?", (account_id,))
    conn.execute("DELETE FROM erp_wholesale_accounts WHERE id = ?", (account_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True, deleted_orders=len(order_ids))


@app.post("/api/erp/wholesale-orders/<int:order_id>/accept")
def erp_accept_wholesale_order(order_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    if not w:
        conn.close()
        return jsonify(error="order not found"), 404
    fulf = _erp_get_fulfillment(conn, "wholesale", order_id)
    if not fulf or fulf["status"] != "submitted":
        conn.close()
        return jsonify(error="only submitted orders can be accepted"), 400
    err_msg = _erp_set_fulfillment(conn, "wholesale", order_id, "accepted", actor,
                                   (data.get("note") or "").strip())
    if err_msg:
        conn.close()
        return jsonify(error=err_msg), 400
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (w["account_id"],)).fetchone()
    conn.commit()
    conn.close()
    if acct and acct["email"]:
        _send_order_accepted_email(acct["email"], w["order_number"], acct["name"])
    return jsonify(ok=True, status="accepted")


@app.post("/api/erp/wholesale-orders/<int:order_id>/decline")
def erp_decline_wholesale_order(order_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    note = (data.get("note") or "").strip()
    conn = db()
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    if not w:
        conn.close()
        return jsonify(error="order not found"), 404
    fulf = _erp_get_fulfillment(conn, "wholesale", order_id)
    if not fulf or fulf["status"] != "submitted":
        conn.close()
        return jsonify(error="only submitted orders can be declined"), 400
    err_msg = _erp_set_fulfillment(conn, "wholesale", order_id, "cancelled", actor,
                                   note or "declined")
    if err_msg:
        conn.close()
        return jsonify(error=err_msg), 400
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (w["account_id"],)).fetchone()
    conn.commit()
    conn.close()
    if acct and acct["email"]:
        _send_order_declined_email(acct["email"], w["order_number"], acct["name"], note)
    return jsonify(ok=True, status="cancelled")


@app.get("/api/erp/wholesale-orders/<int:order_id>/production")
def erp_wholesale_production(order_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    if not w:
        conn.close()
        return jsonify(error="order not found"), 404
    lines = [dict(l) for l in conn.execute(
        "SELECT * FROM erp_order_production_lines WHERE order_id = ? ORDER BY id",
        (order_id,)).fetchall()]
    done, total = _erp_production_progress(conn, order_id)
    conn.close()
    return jsonify(lines=lines, done=done, total=total)


@app.post("/api/erp/wholesale-orders/<int:order_id>/production/<int:line_id>/done")
def erp_wholesale_production_done(order_id, line_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    line = conn.execute("SELECT * FROM erp_order_production_lines WHERE id = ?"
                        " AND order_id = ?", (line_id, order_id)).fetchone()
    if not line:
        conn.close()
        return jsonify(error="production line not found"), 404
    done = 1 if data.get("done", True) else 0
    now = datetime.now(timezone.utc).isoformat()
    conn.execute("UPDATE erp_order_production_lines SET done = ?, done_by = ?,"
                 " done_at = ? WHERE id = ?",
                 (done, actor if done else "", now if done else "", line_id))
    conn.commit()
    d, t = _erp_production_progress(conn, order_id)
    conn.close()
    return jsonify(ok=True, done=d, total=t)


@app.get("/api/erp/wholesale-accounts/<int:account_id>/addresses")
def erp_list_wholesale_addresses(account_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    acct = conn.execute("SELECT id FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    rows = [dict(a) for a in conn.execute(
        "SELECT * FROM erp_wholesale_addresses WHERE account_id = ? ORDER BY id",
        (account_id,)).fetchall()]
    conn.close()
    return jsonify(addresses=rows)


@app.post("/api/erp/wholesale-accounts/<int:account_id>/addresses")
def erp_add_wholesale_address(account_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    acct = conn.execute("SELECT id FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        conn.close()
        return jsonify(error="account not found"), 404
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_wholesale_addresses (account_id, label, location_name, street,"
        " city, state, zip, phone, contact_name, contact_email, contact_phone,"
        " active, created_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?)",
        (account_id, (data.get("label") or "").strip(),
         (data.get("location_name") or "").strip(),
         (data.get("street") or "").strip(), (data.get("city") or "").strip(),
         (data.get("state") or "").strip(), (data.get("zip") or "").strip(),
         (data.get("phone") or "").strip(),
         (data.get("contact_name") or "").strip(),
         (data.get("contact_email") or "").strip(),
         (data.get("contact_phone") or "").strip(), now))
    addr = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?",
                        (cur.lastrowid,)).fetchone()
    conn.commit()
    conn.close()
    return jsonify(address=dict(addr)), 201


@app.put("/api/erp/wholesale-accounts/addresses/<int:addr_id>")
def erp_update_wholesale_address(addr_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    addr = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?",
                        (addr_id,)).fetchone()
    if not addr:
        conn.close()
        return jsonify(error="address not found"), 404
    fields = {}
    for key in ("label", "location_name", "street", "city", "state", "zip", "phone",
                "contact_name", "contact_email", "contact_phone"):
        if key in data:
            fields[key] = (data.get(key) or "").strip()
    if "active" in data:
        fields["active"] = 1 if data.get("active") else 0
    if fields:
        sets = ", ".join("%s = ?" % k for k in fields)
        conn.execute("UPDATE erp_wholesale_addresses SET %s WHERE id = ?" % sets,
                     tuple(fields.values()) + (addr_id,))
        conn.commit()
    addr = conn.execute("SELECT * FROM erp_wholesale_addresses WHERE id = ?",
                        (addr_id,)).fetchone()
    conn.close()
    return jsonify(address=dict(addr))


@app.get("/api/erp/flavor-categories")
def erp_list_flavor_categories():
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    rows = [dict(r) for r in conn.execute(
        "SELECT flavor_name, category FROM erp_flavor_categories"
        " ORDER BY category, flavor_name").fetchall()]
    conn.close()
    return jsonify(categories=rows)


@app.put("/api/erp/flavor-categories")
def erp_update_flavor_categories():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    cats = data.get("categories") or {}
    if not isinstance(cats, dict) or not cats:
        return jsonify(error="categories object is required"), 400
    conn = db()
    for flavor, cat in cats.items():
        if cat not in ("savory", "sweet"):
            conn.close()
            return jsonify(error="invalid category for '%s'" % flavor), 400
        conn.execute("UPDATE erp_flavor_categories SET category = ? WHERE flavor_name = ?",
                     (cat, flavor))
    conn.commit()
    conn.close()
    return jsonify(ok=True, updated=len(cats))


# ---------------- batch <-> order links ----------------

@app.get("/api/erp/batches/<int:batch_id>/orders")
def erp_batch_order_links(batch_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    links = [_erp_batch_link_dict(conn, l) for l in conn.execute(
        "SELECT * FROM erp_batch_orders WHERE batch_id = ? ORDER BY id",
        (batch_id,)).fetchall()]
    conn.close()
    return jsonify(links=links)


@app.post("/api/erp/batches/<int:batch_id>/orders")
def erp_link_batch_order(batch_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    source = (data.get("order_source") or "").strip()
    order_id = data.get("order_id")
    if source not in _ERP_ORDER_SOURCES:
        return jsonify(error="valid order_source is required"), 400
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    if batch["status"] in ("completed", "reversed", "cancelled"):
        conn.close()
        return jsonify(error="cannot link orders to a %s batch" % batch["status"]), 400
    order = _erp_order_brief(conn, source, order_id)
    if not order:
        conn.close()
        return jsonify(error="order not found"), 404
    try:
        qty = float(data.get("qty_bags") or 0)
    except (TypeError, ValueError):
        conn.close()
        return jsonify(error="qty_bags must be a number"), 400
    if qty <= 0:
        conn.close()
        return jsonify(error="qty_bags must be greater than zero"), 400
    dup = conn.execute("SELECT id FROM erp_batch_orders WHERE batch_id = ?"
                       " AND order_source = ? AND order_id = ?",
                       (batch_id, source, order_id)).fetchone()
    if dup:
        conn.close()
        return jsonify(error="batch is already linked to this order"), 400
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_batch_orders (batch_id, order_source, order_id, qty_bags,"
        " created_by, created_at) VALUES (?, ?, ?, ?, ?, ?)",
        (batch_id, source, order_id, qty, actor, now))
    link = conn.execute("SELECT * FROM erp_batch_orders WHERE id = ?",
                        (cur.lastrowid,)).fetchone()
    out = _erp_batch_link_dict(conn, link)
    conn.commit()
    conn.close()
    return jsonify(link=out), 201


@app.delete("/api/erp/batches/<int:batch_id>/orders/<int:link_id>")
def erp_unlink_batch_order(batch_id, link_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    batch = _erp_get_batch(conn, batch_id)
    if not batch:
        conn.close()
        return jsonify(error="batch not found"), 404
    if batch["status"] in ("completed", "reversed", "cancelled"):
        conn.close()
        return jsonify(error="cannot unlink orders from a %s batch;"
                              " post a correcting entry instead" % batch["status"]), 400
    link = conn.execute("SELECT * FROM erp_batch_orders WHERE id = ? AND batch_id = ?",
                        (link_id, batch_id)).fetchone()
    if not link:
        conn.close()
        return jsonify(error="link not found"), 404
    conn.execute("DELETE FROM erp_batch_orders WHERE id = ?", (link_id,))
    conn.commit()
    conn.close()
    return jsonify(ok=True)


@app.get("/api/erp/orders/<source>/<int:order_id>/trace")
def erp_order_trace(source, order_id):
    """Traceability: order -> production batches -> ingredient lots."""
    actor, err = _require_erp()
    if err:
        return err
    if source not in _ERP_ORDER_SOURCES:
        return jsonify(error="unknown source"), 404
    conn = db()
    order = _erp_order_brief(conn, source, order_id)
    if not order:
        conn.close()
        return jsonify(error="order not found"), 404
    batches = []
    for l in conn.execute("SELECT * FROM erp_batch_orders WHERE order_source = ?"
                          " AND order_id = ? ORDER BY id",
                          (source, order_id)).fetchall():
        b = conn.execute("SELECT * FROM erp_production_batches WHERE id = ?",
                         (l["batch_id"],)).fetchone()
        if not b:
            continue
        ingredients = [dict(r) for r in conn.execute(
            "SELECT bi.*, i.sku, i.name AS item_name FROM erp_batch_ingredients bi"
            " JOIN erp_items i ON i.id = bi.item_id"
            " WHERE bi.batch_id = ? ORDER BY bi.id", (b["id"],)).fetchall()]
        batches.append({"batch_id": b["id"], "batch_number": b["batch_number"],
                        "lot_code": b["lot_code"], "expiry_date": b["expiry_date"],
                        "batch_status": b["status"], "qty_bags": l["qty_bags"],
                        "ingredients": ingredients})
    conn.close()
    return jsonify(order=order, batches=batches)


# ---------------- ERP Phase 3: EDI module (provider-agnostic) ----------------
# Minimal X12 engine for the grocery subset: parse inbound 850, generate
# outbound 856 + 810, record 997 functional acks. Secrets never touch the DB:
# partner config holds refs only; webhook keys are stored as hashes.

_EDI_TRANSPORTS = ("manual-file", "sftp", "api", "webhook")
_EDI_DOC_TYPES = ("850", "855", "856", "810", "997")
_EDI_DOC_STATUSES = ("received", "parsed", "mapped", "queued", "sent",
                     "acked", "failed")
_EDI_CONFIG_FORBIDDEN = ("password", "secret", "private_key", "api_key",
                         "passphrase", "webhook_key")


def _edi_sanitize_config(cfg):
    """Drop anything that looks like a secret from partner config before
    storage. Keys ending in _hash (e.g. webhook_key_hash) are digests, not
    secrets, and are kept."""
    if not isinstance(cfg, dict):
        return {}
    clean = {}
    for k, v in cfg.items():
        kl = str(k).lower()
        if kl.endswith("_hash"):
            clean[k] = v
            continue
        if any(frag in kl for frag in _EDI_CONFIG_FORBIDDEN):
            continue
        if isinstance(v, dict):
            clean[k] = _edi_sanitize_config(v)
        else:
            clean[k] = v
    return clean


def _edi_config(conn, partner):
    try:
        cfg = json.loads(partner["config_json"] or "{}")
    except (TypeError, ValueError):
        cfg = {}
    return cfg if isinstance(cfg, dict) else {}


def _edi_partner_public(conn, p):
    cfg = _edi_config(conn, p)
    return {"id": p["id"], "name": p["name"], "provider": p["provider"],
            "transport": p["transport"], "active": bool(p["active"]),
            "has_webhook_key": bool(cfg.get("webhook_key_hash")),
            "created_at": p["created_at"]}


def _edi_partner_detail(conn, p):
    d = _edi_partner_public(conn, p)
    cfg = _edi_config(conn, p)
    cfg = dict(cfg)
    cfg.pop("webhook_key_hash", None)
    d["config"] = cfg
    return d


def _edi_new_webhook_key():
    return "edip_" + secrets.token_urlsafe(24)


def _edi_key_hash(key):
    return hashlib.sha256(key.encode("utf-8")).hexdigest()


# ----- X12 parsing -----

def _x12_split_segments(text):
    t = (text or "").strip()
    if not t:
        return []
    if "~" in t:
        parts = t.split("~")
    else:
        parts = re.split(r"[\r\n]+", t)
    return [p.strip() for p in parts if p.strip()]


def _x12_parse_850(text):
    """Parse an X12 850 purchase order (grocery subset).
    Returns (parsed_dict, errors). Non-empty errors => reject the document."""
    errors = []
    segs = _x12_split_segments(text)
    if not segs:
        return None, ["empty document"]
    if not segs[0].startswith("ISA"):
        return None, ["document must start with an ISA segment"]
    sep = segs[0][3:4] or "*"
    isa = segs[0].split(sep)
    if len(isa) < 16:
        return None, ["malformed ISA segment (expected 16 elements)"]

    def is_seg(s, tag):
        return s.startswith(tag + sep)

    idx = {s.split(sep)[0]: i for i, s in enumerate(segs)}
    st_i = next((i for i, s in enumerate(segs) if is_seg(s, "ST")), None)
    if st_i is None:
        return None, ["missing ST segment"]
    st = segs[st_i].split(sep)
    if len(st) < 2 or st[1] != "850":
        return None, ["not an 850 transaction (ST01=%s)" % (st[1] if len(st) > 1 else "?")]
    se_i = next((i for i in range(st_i + 1, len(segs)) if is_seg(segs[i], "SE")), None)
    if se_i is None:
        errors.append("missing SE segment")
    else:
        se = segs[se_i].split(sep)
        try:
            claimed = int(se[1])
        except (IndexError, ValueError):
            claimed = -1
        actual = se_i - st_i + 1
        if claimed != actual:
            errors.append("SE segment count mismatch: claimed %s, actual %s"
                          % (se[1] if len(se) > 1 else "?", actual))
    ge_i = next((i for i, s in enumerate(segs) if is_seg(s, "GE")), None)
    if ge_i is None:
        errors.append("missing GE segment")
    if not any(is_seg(s, "IEA") for s in segs):
        errors.append("missing IEA segment")

    beg = next((s for s in segs if is_seg(s, "BEG")), None)
    if beg is None:
        errors.append("missing BEG segment (purchase order header)")
        po_number, po_date = "", ""
    else:
        be = beg.split(sep)
        po_number = be[3] if len(be) > 3 else ""
        po_date = be[5] if len(be) > 5 else ""
        if not po_number:
            errors.append("BEG03 purchase order number is missing")

    def n1(code):
        for s in segs:
            e = s.split(sep)
            if e[0] == "N1" and len(e) > 1 and e[1] == code:
                return {"qualifier": e[3] if len(e) > 3 else "",
                        "id": e[4] if len(e) > 4 else "",
                        "name": e[2] if len(e) > 2 else ""}
        return {"qualifier": "", "id": "", "name": ""}

    lines = []
    cur = None
    for s in segs:
        e = s.split(sep)
        if e[0] == "PO1":
            if cur:
                lines.append(cur)
            try:
                qty = float(e[2]) if len(e) > 2 and e[2] else 0
            except ValueError:
                qty = -1
            try:
                price_cents = int(round(float(e[4]) * 100)) if len(e) > 4 and e[4] else 0
            except ValueError:
                price_cents = -1
            cur = {"line": int(e[1]) if len(e) > 1 and e[1].isdigit() else len(lines) + 1,
                   "qty": qty, "uom": e[3] if len(e) > 3 else "",
                   "unit_price_cents": price_cents,
                   "product_id": e[7] if len(e) > 7 else "",
                   "description": ""}
            if qty <= 0:
                errors.append("PO1 line %s: quantity must be > 0" % cur["line"])
            if price_cents < 0:
                errors.append("PO1 line %s: unit price is not a number" % cur["line"])
        elif e[0] == "PID" and cur is not None:
            if len(e) > 5 and e[5]:
                cur["description"] = e[5]
    if cur:
        lines.append(cur)
    if not lines:
        errors.append("no PO1 line items found")
    ctt = next((s for s in segs if is_seg(s, "CTT")), None)
    if ctt:
        ce = ctt.split(sep)
        try:
            if int(ce[1]) != len(lines):
                errors.append("CTT line count %s does not match %d PO1 segments"
                              % (ce[1], len(lines)))
        except (IndexError, ValueError):
            errors.append("malformed CTT segment")
    parsed = {"doc_type": "850", "po_number": po_number, "po_date": po_date,
              "ship_to": n1("ST"), "bill_to": n1("BT"), "lines": lines,
              "total_lines": len(lines),
              "control": {"isa13": isa[13] if len(isa) > 13 else "",
                         "sender": (isa[6] if len(isa) > 6 else "").strip(),
                         "receiver": (isa[8] if len(isa) > 8 else "").strip()}}
    return parsed, errors


# ----- X12 generation -----

def _edi_next_control(conn):
    n = conn.execute("SELECT COALESCE(MAX(id), 0) + 1 AS n"
                     " FROM erp_edi_documents").fetchone()["n"]
    return int(n)


def _x12_pad(s, n):
    s = (s or "")[:n]
    return s + " " * (n - len(s))


def _x12_envelope(doc_type, gs_code, body, sender, receiver, ctrl):
    """Wrap ST..CTT body segments in ISA/GS/GE/IEA. Returns full X12 string."""
    now = datetime.now(timezone.utc)
    ymd = now.strftime("%Y%m%d")
    hm = now.strftime("%H%M")
    isa13 = "%09d" % (ctrl % 1000000000)
    st02 = "%04d" % (ctrl % 10000)
    segs = []
    segs.append("ISA*00*%s*00*%s*ZZ*%s*ZZ*%s*%s*%s*U*00401*%s*0*P*>"
                % (" " * 10, " " * 10, _x12_pad(sender, 15),
                   _x12_pad(receiver, 15), now.strftime("%y%m%d"), hm, isa13))
    segs.append("GS*%s*%s*%s*%s*%s*%d*X*004010"
                % (gs_code, sender or "POPALICIOUS", receiver or "PARTNER",
                   ymd, hm, ctrl))
    body = [b if b.startswith("ST*") else b for b in body]
    body[0] = "ST*%s*%s" % (doc_type, st02)
    segs.extend(body)
    segs.append("SE*%d*%s" % (len(body) + 1, st02))
    segs.append("GE*1*%d" % ctrl)
    segs.append("IEA*1*%s" % isa13)
    return "~".join(segs) + "~"


def _x12_build_856(order, lines, partner_cfg, ctrl):
    """Ship notice for an order. lines: [{line, qty, product_id, description}]."""
    sender = (partner_cfg.get("isa_sender") or "POPALICIOUS")
    receiver = (partner_cfg.get("isa_receiver") or "PARTNER")
    now = datetime.now(timezone.utc)
    ymd = now.strftime("%Y%m%d")
    ship_id = "SHP-%s-%d" % ((order.get("number") or "NA").replace("#", ""), ctrl)
    ship_to = order.get("ship_to") or {}
    body = [
        "ST*856*0001",
        "BSN*00*%s*%s*%s" % (ship_id, ymd, now.strftime("%H%M")),
        "DTM*011*%s" % ymd,
        "N1*ST*%s*%s*%s" % (ship_to.get("name") or "Customer",
                            ship_to.get("qualifier") or "92",
                            ship_to.get("id") or ""),
        "HL*1**S",
    ]
    hl = 2
    body.append("HL*%d**O*1" % hl)
    hl += 1
    body.append("PRF*%s*%s" % (order.get("po_number") or order.get("number") or "",
                               order.get("po_date") or ymd))
    for ln in lines:
        body.append("HL*%d**I*2" % hl)
        hl += 1
        body.append("LIN**%s*%s" % (ln.get("id_qualifier") or "VP",
                                    ln.get("product_id") or ""))
        body.append("SN1**%s*EA" % _erp_fmt_qty(ln.get("qty") or 0))
    body.append("CTT*%d" % len(lines))
    return _x12_envelope("856", "SH", body, sender, receiver, ctrl)


def _x12_build_810(order, lines, partner_cfg, ctrl):
    """Invoice for a wholesale order."""
    sender = (partner_cfg.get("isa_sender") or "POPALICIOUS")
    receiver = (partner_cfg.get("isa_receiver") or "PARTNER")
    now = datetime.now(timezone.utc)
    ymd = now.strftime("%Y%m%d")
    inv_num = "INV-%s" % (order.get("number") or ctrl)
    ship_to = order.get("ship_to") or {}
    total_cents = 0
    body = [
        "ST*810*0001",
        "BIG*%s*%s*%s*%s" % (ymd, inv_num, order.get("po_date") or ymd,
                             order.get("po_number") or order.get("number") or ""),
        "N1*ST*%s*%s*%s" % (ship_to.get("name") or "Customer",
                            ship_to.get("qualifier") or "92",
                            ship_to.get("id") or ""),
    ]
    for i, ln in enumerate(lines, 1):
        qty = float(ln.get("qty") or 0)
        unit_cents = int(ln.get("unit_price_cents") or 0)
        total_cents += int(round(qty * unit_cents))
        body.append("IT1*%d*%s*EA*%.2f**%s*%s"
                    % (i, _erp_fmt_qty(qty), unit_cents / 100.0,
                       ln.get("id_qualifier") or "VP", ln.get("product_id") or ""))
    body.append("TDS*%d" % total_cents)
    body.append("CTT*%d" % len(lines))
    return _x12_envelope("810", "IN", body, sender, receiver, ctrl), inv_num


def _x12_build_997(inbound_ctrl, partner_cfg, ctrl):
    """Functional acknowledgement for a received 850."""
    sender = (partner_cfg.get("isa_sender") or "POPALICIOUS")
    receiver = (partner_cfg.get("isa_receiver") or "PARTNER")
    body = [
        "ST*997*0001",
        "AK1*PO*%s" % (inbound_ctrl.get("gs06") or "1"),
        "AK2*850*%s" % (inbound_ctrl.get("st02") or "1"),
        "AK5*A",
        "AK9*A*1*1*1",
    ]
    return _x12_envelope("997", "FA", body, sender, receiver, ctrl)


# ----- EDI document helpers -----

def _edi_doc_dict(conn, d, include_content=False):
    p = conn.execute("SELECT name FROM erp_edi_partners WHERE id = ?",
                     (d["partner_id"],)).fetchone()
    try:
        parsed = json.loads(d["parsed_json"] or "{}")
    except (TypeError, ValueError):
        parsed = {}
    order_number = ""
    if d["order_source"] and d["order_id"]:
        o = _erp_order_brief(conn, d["order_source"], d["order_id"])
        order_number = o["number"] if o else ""
    out = {"id": d["id"], "partner_id": d["partner_id"],
           "partner_name": p["name"] if p else "",
           "direction": d["direction"], "doc_type": d["doc_type"],
           "status": d["status"], "order_source": d["order_source"],
           "order_id": d["order_id"], "order_number": order_number,
           "created_at": d["created_at"]}
    if include_content:
        out["raw_text"] = d["raw_text"]
        out["x12"] = d["raw_text"]
        out["parsed"] = parsed
    return out


def _edi_match_account(conn, partner, parsed):
    """Match a parsed 850 to a wholesale account via partner config.
    Returns (account_row, match_note, error). error is None on success."""
    cfg = _edi_config(conn, partner)
    ship_to_id = (parsed.get("ship_to") or {}).get("id") or ""
    account_id = None
    note = ""
    ship_map = cfg.get("ship_to_map") or {}
    if ship_to_id and str(ship_to_id) in {str(k) for k in ship_map}:
        for k, v in ship_map.items():
            if str(k) == str(ship_to_id):
                account_id = v
                note = "ship-to %s" % ship_to_id
                break
    elif cfg.get("account_id"):
        account_id = cfg["account_id"]
        note = "partner default account"
    if not account_id:
        return None, "", ("no wholesale account mapped for ship-to '%s'"
                          % (ship_to_id or "?"))
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (account_id,)).fetchone()
    if not acct:
        return None, "", "mapped account id %s does not exist" % account_id
    if not acct["active"]:
        return None, "", "mapped account '%s' is inactive" % acct["name"]
    return acct, note, None


def _edi_create_997(conn, partner, parsed, actor):
    cfg = _edi_config(conn, partner)
    ctrl = _edi_next_control(conn)
    x12 = _x12_build_997(parsed.get("control") or {}, cfg, ctrl)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_edi_documents (partner_id, direction, doc_type, status,"
        " raw_text, parsed_json, created_at)"
        " VALUES (?, 'outbound', '997', 'sent', ?, ?, ?)",
        (partner["id"], x12, json.dumps({"ack_for": "850"}), now))
    return cur.lastrowid


def _edi_map_850_to_order(conn, doc, parsed, partner, actor):
    """Create a wholesale order from a parsed 850. Returns (order_brief, error)."""
    acct, _note, match_err = _edi_match_account(conn, partner, parsed)
    if match_err:
        return None, match_err
    lines = []
    for i, ln in enumerate(parsed.get("lines") or [], 1):
        flavor = (ln.get("description") or ln.get("product_id") or "").strip()
        if not flavor:
            return None, "PO1 line %d: no product id or description" % i
        qty = float(ln.get("qty") or 0)
        if qty <= 0:
            return None, "PO1 line %d: quantity must be > 0" % i
        unit = int(ln.get("unit_price_cents") or acct["price_per_bag_cents"] or 400)
        if unit <= 0:
            return None, "PO1 line %d: unit price must be > 0" % i
        lines.append({"flavor_name": flavor, "qty_bags": qty,
                      "unit_price_cents": unit,
                      "line_total_cents": int(round(qty * unit))})
    if not lines:
        return None, "no order lines in 850"
    now = datetime.now(timezone.utc).isoformat()
    order_number = _erp_next_wholesale_number(conn)
    cur = conn.execute(
        "INSERT INTO erp_wholesale_orders (order_number, account_id, status, order_date,"
        " due_date, notes, via_edi, edi_document_id, created_by, created_at)"
        " VALUES (?, ?, 'new', ?, '', ?, 1, ?, ?, ?)",
        (order_number, acct["id"], parsed.get("po_date") or "",
         "EDI 850 %s" % (parsed.get("po_number") or ""), doc["id"], actor, now))
    order_id = cur.lastrowid
    for li in lines:
        conn.execute(
            "INSERT INTO erp_wholesale_order_lines (order_id, flavor_name, qty_bags,"
            " unit_price_cents, line_total_cents) VALUES (?, ?, ?, ?, ?)",
            (order_id, li["flavor_name"], li["qty_bags"],
             li["unit_price_cents"], li["line_total_cents"]))
    _erp_set_fulfillment(conn, "wholesale", order_id, "new", actor,
                         "created from EDI 850 %s" % parsed.get("po_number"))
    conn.execute("UPDATE erp_edi_documents SET status = 'mapped',"
                 " order_source = 'wholesale', order_id = ? WHERE id = ?",
                 (order_id, doc["id"]))
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    return _erp_wholesale_order_brief(conn, w), None


def _edi_parse_and_store_inbound(conn, partner, content, actor):
    """Shared by upload + webhook: detect type, parse, store, ack."""
    segs = _x12_split_segments(content)
    sep = segs[0][3:4] if segs and segs[0].startswith("ISA") else "*"
    st = next((s for s in segs if s.split(sep)[0] == "ST"), None)
    doc_type = ""
    if st:
        parts = st.split(sep)
        doc_type = parts[1] if len(parts) > 1 else ""
    if doc_type != "850":
        return None, "unsupported inbound doc_type '%s' (only 850)" % (doc_type or "?")
    parsed, errors = _x12_parse_850(content)
    now = datetime.now(timezone.utc).isoformat()
    status = "parsed" if not errors else "failed"
    cur = conn.execute(
        "INSERT INTO erp_edi_documents (partner_id, direction, doc_type, status,"
        " raw_text, parsed_json, created_at) VALUES (?, 'inbound', '850', ?, ?, ?, ?)",
        (partner["id"] if partner else 0, status, content,
         json.dumps(parsed or {"errors": errors}), now))
    doc_id = cur.lastrowid
    ack_id = None
    if not errors and partner:
        ack_id = _edi_create_997(conn, partner, parsed, actor)
    doc = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                       (doc_id,)).fetchone()
    preview = {"po_number": (parsed or {}).get("po_number", ""),
               "partner_name": partner["name"] if partner else "",
               "account_name": "", "account_match_note": "",
               "lines": [{"flavor": (l.get("description") or l.get("product_id") or ""),
                          "qty": l.get("qty"), "unit_price_cents": l.get("unit_price_cents")}
                         for l in (parsed or {}).get("lines", [])],
               "errors": errors, "ack_document_id": ack_id}
    if not errors and partner:
        acct, note, match_err = _edi_match_account(conn, partner, parsed)
        if acct:
            preview["account_name"] = acct["name"]
            preview["account_match_note"] = note or ""
        else:
            preview["errors"] = errors + [match_err]
    return doc, preview


# ----- EDI endpoints -----

@app.get("/api/erp/edi-partners")
def erp_list_edi_partners():
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    rows = conn.execute("SELECT * FROM erp_edi_partners ORDER BY name").fetchall()
    out = [_edi_partner_public(conn, r) for r in rows]
    conn.close()
    return jsonify(partners=out)


@app.post("/api/erp/edi-partners")
def erp_create_edi_partner():
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    name = (data.get("name") or "").strip()
    if not name:
        return jsonify(error="name is required"), 400
    transport = (data.get("transport") or "manual-file").strip()
    if transport not in _EDI_TRANSPORTS:
        return jsonify(error="unknown transport"), 400
    cfg = _edi_sanitize_config(data.get("config") or {})
    webhook_key = None
    if transport == "webhook":
        webhook_key = _edi_new_webhook_key()
        cfg["webhook_key_hash"] = _edi_key_hash(webhook_key)
    conn = db()
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_edi_partners (name, provider, transport, config_json,"
        " active, created_by, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)",
        (name, (data.get("provider") or "").strip(), transport,
         json.dumps(cfg), 1 if data.get("active", True) else 0, actor, now))
    p = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                     (cur.lastrowid,)).fetchone()
    out = _edi_partner_detail(conn, p)
    conn.commit()
    conn.close()
    resp = {"partner": out}
    if webhook_key:
        resp["webhook_key"] = webhook_key
    return jsonify(resp), 201


@app.get("/api/erp/edi-partners/<int:partner_id>")
def erp_get_edi_partner(partner_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    p = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                     (partner_id,)).fetchone()
    if not p:
        conn.close()
        return jsonify(error="partner not found"), 404
    out = _edi_partner_detail(conn, p)
    conn.close()
    return jsonify(partner=out)


@app.put("/api/erp/edi-partners/<int:partner_id>")
def erp_update_edi_partner(partner_id):
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True) or {}
    conn = db()
    p = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                     (partner_id,)).fetchone()
    if not p:
        conn.close()
        return jsonify(error="partner not found"), 404
    fields = {}
    if "name" in data:
        if not (data.get("name") or "").strip():
            conn.close()
            return jsonify(error="name is required"), 400
        fields["name"] = data["name"].strip()
    if "provider" in data:
        fields["provider"] = (data.get("provider") or "").strip()
    if "transport" in data:
        t = (data.get("transport") or "").strip()
        if t not in _EDI_TRANSPORTS:
            conn.close()
            return jsonify(error="unknown transport"), 400
        fields["transport"] = t
    if "active" in data:
        fields["active"] = 1 if data.get("active") else 0
    cfg = _edi_config(conn, p)
    webhook_key = None
    if isinstance(data.get("config"), dict):
        for k, v in _edi_sanitize_config(data["config"]).items():
            cfg[k] = v
    if data.get("rotate_webhook_key"):
        webhook_key = _edi_new_webhook_key()
        cfg["webhook_key_hash"] = _edi_key_hash(webhook_key)
    fields["config_json"] = json.dumps(cfg)
    sets = ", ".join("%s = ?" % k for k in fields)
    conn.execute("UPDATE erp_edi_partners SET %s WHERE id = ?" % sets,
                 tuple(fields.values()) + (partner_id,))
    conn.commit()
    p = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                     (partner_id,)).fetchone()
    out = _edi_partner_detail(conn, p)
    conn.close()
    resp = {"partner": out}
    if webhook_key:
        resp["webhook_key"] = webhook_key
    return jsonify(resp)


@app.get("/api/erp/edi-documents")
def erp_list_edi_documents():
    actor, err = _require_erp()
    if err:
        return err
    direction = (request.args.get("direction") or "").strip()
    doc_type = (request.args.get("doc_type") or "").strip()
    status = (request.args.get("status") or "").strip()
    if direction and direction not in ("inbound", "outbound"):
        return jsonify(error="unknown direction"), 400
    if doc_type and doc_type not in _EDI_DOC_TYPES:
        return jsonify(error="unknown doc_type"), 400
    if status and status not in _EDI_DOC_STATUSES:
        return jsonify(error="unknown status"), 400
    conn = db()
    q = "SELECT * FROM erp_edi_documents WHERE 1=1"
    args = []
    if direction:
        q += " AND direction = ?"
        args.append(direction)
    if doc_type:
        q += " AND doc_type = ?"
        args.append(doc_type)
    if status:
        q += " AND status = ?"
        args.append(status)
    q += " ORDER BY id DESC"
    out = [_edi_doc_dict(conn, d) for d in conn.execute(q, args).fetchall()]
    conn.close()
    return jsonify(documents=out)


@app.get("/api/erp/edi-documents/<int:doc_id>")
def erp_get_edi_document(doc_id):
    actor, err = _require_erp()
    if err:
        return err
    conn = db()
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (doc_id,)).fetchone()
    if not d:
        conn.close()
        return jsonify(error="document not found"), 404
    out = _edi_doc_dict(conn, d, include_content=True)
    conn.close()
    return jsonify(document=out)


@app.post("/api/erp/edi-documents/upload")
def erp_edi_upload():
    """Manual X12 upload: parse -> preview. Confirm via POST .../id/map."""
    actor, err = _require_erp_admin()
    if err:
        return err
    content = ""
    partner_id = 0
    filename = ""
    if request.files and "file" in request.files:
        f = request.files["file"]
        filename = f.filename or ""
        content = f.read().decode("utf-8", "ignore")
        partner_id = int(request.form.get("partner_id") or 0)
    else:
        data = request.get_json(force=True, silent=True) or {}
        content = data.get("content") or ""
        filename = data.get("filename") or ""
        partner_id = int(data.get("partner_id") or 0)
    if not content.strip():
        return jsonify(error="X12 content is required"), 400
    conn = db()
    partner = None
    if partner_id:
        partner = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                               (partner_id,)).fetchone()
        if not partner:
            conn.close()
            return jsonify(error="partner not found"), 404
    else:
        # auto-match by ISA sender id against partner config
        segs = _x12_split_segments(content)
        sender = ""
        if segs and segs[0].startswith("ISA"):
            sep = segs[0][3:4] or "*"
            isa = segs[0].split(sep)
            sender = (isa[6] if len(isa) > 6 else "").strip()
        if sender:
            for p in conn.execute(
                    "SELECT * FROM erp_edi_partners WHERE active = 1").fetchall():
                cfg = _edi_config(conn, p)
                ids = cfg.get("isa_ids") or []
                if sender in [str(x).strip() for x in ids]:
                    partner = p
                    break
    doc, preview = _edi_parse_and_store_inbound(conn, partner, content, actor)
    if doc is None:
        conn.close()
        return jsonify(error=preview), 400
    conn.commit()
    out = _edi_doc_dict(conn, doc)
    conn.close()
    return jsonify(document=out, preview=preview), 201


@app.post("/api/erp/edi-documents/<int:doc_id>/map")
def erp_edi_map_document(doc_id):
    """Confirm: map a parsed inbound 850 to a wholesale order."""
    actor, err = _require_erp_admin()
    if err:
        return err
    conn = db()
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (doc_id,)).fetchone()
    if not d:
        conn.close()
        return jsonify(error="document not found"), 404
    if d["direction"] != "inbound" or d["doc_type"] != "850":
        conn.close()
        return jsonify(error="only inbound 850 documents can be mapped"), 400
    if d["status"] == "mapped":
        conn.close()
        return jsonify(error="document is already mapped"), 400
    if d["status"] != "parsed":
        conn.close()
        return jsonify(error="document must parse cleanly before mapping"), 400
    partner = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                           (d["partner_id"],)).fetchone()
    if not partner:
        conn.close()
        return jsonify(error="no trading partner on this document"), 400
    try:
        parsed = json.loads(d["parsed_json"] or "{}")
    except (TypeError, ValueError):
        parsed = {}
    order, map_err = _edi_map_850_to_order(conn, d, parsed, partner, actor)
    if map_err:
        conn.close()
        return jsonify(error=map_err), 400
    conn.commit()
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (doc_id,)).fetchone()
    conn.close()
    return jsonify(ok=True, order=order, document=_edi_doc_dict_careful(d))


def _edi_doc_dict_careful(d):
    # _edi_doc_dict needs a conn for partner/order lookups; used only post-commit
    # where a fresh conn is cheap. Kept separate to avoid signature churn.
    conn = db()
    try:
        return _edi_doc_dict(conn, d)
    finally:
        conn.close()


@app.post("/api/erp/edi-documents/<int:doc_id>/retry")
def erp_edi_retry_document(doc_id):
    """Re-run parse/map for inbound docs; re-queue or mark sent for outbound."""
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True, silent=True) or {}
    conn = db()
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (doc_id,)).fetchone()
    if not d:
        conn.close()
        return jsonify(error="document not found"), 404
    if d["direction"] == "inbound":
        if d["status"] == "mapped":
            conn.close()
            return jsonify(error="document is already mapped"), 400
        parsed, errors = _x12_parse_850(d["raw_text"])
        status = "parsed" if not errors else "failed"
        conn.execute("UPDATE erp_edi_documents SET status = ?, parsed_json = ?"
                     " WHERE id = ?",
                     (status, json.dumps(parsed or {"errors": errors}), doc_id))
        conn.commit()
        d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                         (doc_id,)).fetchone()
        conn.close()
        return jsonify(document=_edi_doc_dict_careful(d))
    # outbound
    if data.get("mark_sent"):
        conn.execute("UPDATE erp_edi_documents SET status = 'sent' WHERE id = ?",
                     (doc_id,))
        conn.commit()
    elif d["status"] == "failed":
        conn.execute("UPDATE erp_edi_documents SET status = 'queued' WHERE id = ?",
                     (doc_id,))
        conn.commit()
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (doc_id,)).fetchone()
    conn.close()
    return jsonify(document=_edi_doc_dict_careful(d))


@app.post("/api/erp/wholesale-orders/<int:order_id>/edi-810")
def erp_wholesale_order_edi810(order_id):
    """Generate an 810 invoice X12 for a wholesale order (queued for transport)."""
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True, silent=True) or {}
    conn = db()
    w = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                     (order_id,)).fetchone()
    if not w:
        conn.close()
        return jsonify(error="order not found"), 404
    partner = None
    if data.get("partner_id"):
        partner = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                               (data["partner_id"],)).fetchone()
    if not partner and w["edi_document_id"]:
        src = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                           (w["edi_document_id"],)).fetchone()
        if src:
            partner = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                                   (src["partner_id"],)).fetchone()
    if not partner:
        partner = conn.execute("SELECT * FROM erp_edi_partners WHERE active = 1"
                               " ORDER BY id LIMIT 1").fetchone()
    if not partner:
        conn.close()
        return jsonify(error="no EDI partner configured"), 400
    cfg = _edi_config(conn, partner)
    acct = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                        (w["account_id"],)).fetchone()
    lines = [{"line": i + 1, "qty": float(l["qty_bags"]),
              "unit_price_cents": int(l["unit_price_cents"]),
              "product_id": (l["flavor_name"] or "")[:30].upper().replace(" ", "_"),
              "description": l["flavor_name"]}
             for i, l in enumerate(conn.execute(
                 "SELECT * FROM erp_wholesale_order_lines WHERE order_id = ?"
                 " ORDER BY id", (order_id,)).fetchall())]
    if not lines:
        conn.close()
        return jsonify(error="order has no lines"), 400
    order = {"number": w["order_number"], "po_number": w["order_number"],
             "po_date": w["order_date"],
             "ship_to": {"name": (acct["name"] if acct else "")[:40],
                         "qualifier": "92", "id": str(acct["id"]) if acct else ""}}
    ctrl = _edi_next_control(conn)
    x12, inv_num = _x12_build_810(order, lines, cfg, ctrl)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_edi_documents (partner_id, direction, doc_type, status,"
        " raw_text, parsed_json, order_source, order_id, created_at)"
        " VALUES (?, 'outbound', '810', 'queued', ?, ?, 'wholesale', ?, ?)",
        (partner["id"], x12,
         json.dumps({"invoice_number": inv_num,
                     "order_number": w["order_number"]}), order_id, now))
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (cur.lastrowid,)).fetchone()
    out = _edi_doc_dict(conn, d, include_content=True)
    conn.commit()
    conn.close()
    return jsonify(document=out), 201


@app.post("/api/erp/orders/<source>/<int:order_id>/edi-856")
def erp_order_edi856(source, order_id):
    """Generate an 856 ship-notice X12 for an order (queued for transport)."""
    actor, err = _require_erp_admin()
    if err:
        return err
    data = request.get_json(force=True, silent=True) or {}
    if source not in _ERP_ORDER_SOURCES:
        return jsonify(error="unknown source"), 404
    conn = db()
    order = _erp_order_brief(conn, source, order_id)
    if not order:
        conn.close()
        return jsonify(error="order not found"), 404
    partner = None
    if data.get("partner_id"):
        partner = conn.execute("SELECT * FROM erp_edi_partners WHERE id = ?",
                               (data["partner_id"],)).fetchone()
    if not partner:
        partner = conn.execute("SELECT * FROM erp_edi_partners WHERE active = 1"
                               " ORDER BY id LIMIT 1").fetchone()
    if not partner:
        conn.close()
        return jsonify(error="no EDI partner configured"), 400
    cfg = _edi_config(conn, partner)
    if source == "wholesale":
        wlines = conn.execute("SELECT * FROM erp_wholesale_order_lines"
                              " WHERE order_id = ? ORDER BY id",
                              (order_id,)).fetchall()
        lines = [{"line": i + 1, "qty": float(l["qty_bags"]),
                  "product_id": (l["flavor_name"] or "")[:30].upper().replace(" ", "_"),
                  "description": l["flavor_name"]}
                 for i, l in enumerate(wlines)]
        ship_name = order.get("account_name") or order.get("customer_name")
    else:
        lines = [{"line": 1, "qty": float(order.get("total_qty") or 0),
                  "product_id": (order.get("number") or "").replace("#", ""),
                  "description": (order.get("items_summary") or "")[:60]}]
        ship_name = order.get("customer_name") or order.get("email")
    if not lines or sum(l["qty"] for l in lines) <= 0:
        conn.close()
        return jsonify(error="order has no shippable quantity"), 400
    o = {"number": order["number"], "po_number": order["number"],
         "ship_to": {"name": (ship_name or "Customer")[:40],
                     "qualifier": "92", "id": str(order_id)}}
    ctrl = _edi_next_control(conn)
    x12 = _x12_build_856(o, lines, cfg, ctrl)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_edi_documents (partner_id, direction, doc_type, status,"
        " raw_text, parsed_json, order_source, order_id, created_at)"
        " VALUES (?, 'outbound', '856', 'queued', ?, ?, ?, ?, ?)",
        (partner["id"], x12,
         json.dumps({"order_number": order["number"], "source": source}),
         source, order_id, now))
    d = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                     (cur.lastrowid,)).fetchone()
    out = _edi_doc_dict(conn, d, include_content=True)
    conn.commit()
    conn.close()
    return jsonify(document=out), 201


@app.post("/api/erp/edi-webhook/<partner_key>")
def erp_edi_webhook(partner_key):
    """Provider push receiver. Key-authenticated ONLY (no login session).
    Accepts JSON {"content": "<X12>"} or a raw X12 body."""
    conn = db()
    digest = _edi_key_hash(partner_key or "")
    partner = None
    for p in conn.execute("SELECT * FROM erp_edi_partners WHERE active = 1"
                          " AND transport = 'webhook'").fetchall():
        cfg = _edi_config(conn, p)
        stored = cfg.get("webhook_key_hash") or ""
        if stored and hmac.compare_digest(stored, digest):
            partner = p
            break
    if not partner:
        conn.close()
        return jsonify(error="invalid partner key"), 401
    data = request.get_json(force=True, silent=True) or {}
    content = data.get("content") or ""
    if not content and request.data:
        try:
            content = request.data.decode("utf-8", "ignore")
        except Exception:
            content = ""
    if not content.strip():
        conn.close()
        return jsonify(error="X12 content is required"), 400
    doc, preview = _edi_parse_and_store_inbound(conn, partner, content,
                                               "edi-webhook")
    if doc is None:
        conn.close()
        return jsonify(error=preview), 400
    mapped_order = None
    if preview and not preview.get("errors") and preview.get("account_name"):
        try:
            parsed = json.loads(doc["parsed_json"] or "{}")
        except (TypeError, ValueError):
            parsed = {}
        mapped_order, map_err = _edi_map_850_to_order(conn, doc, parsed, partner,
                                                     "edi-webhook")
        if map_err:
            preview["errors"] = (preview.get("errors") or []) + [map_err]
    conn.commit()
    doc = conn.execute("SELECT * FROM erp_edi_documents WHERE id = ?",
                       (doc["id"],)).fetchone()
    status = doc["status"]
    doc_id = doc["id"]
    conn.close()
    resp = {"ok": True, "document_id": doc_id, "status": status}
    if mapped_order:
        resp["order"] = mapped_order
    return jsonify(resp), 201


# ================= ERP Phase 4: Reporting + QuickBooks bridge =================
# Spec: files/phase-4-spec.md. All endpoints admin-only (spec section 6).

# ---------- report helpers ----------

def _erp_report_dates(args):
    """Returns (date_from, date_to) as YYYY-MM-DD strings or ('','')."""
    df = (args.get("from") or "").strip()[:10]
    dt = (args.get("to") or "").strip()[:10]
    for d in (df, dt):
        if d and not re.match(r"^\d{4}-\d{2}-\d{2}$", d):
            return None, None
    return df, dt


def _erp_date_where(df, dt, col="created_at"):
    where = []
    params = []
    if df:
        where.append("substr(%s, 1, 10) >= ?" % col)
        params.append(df)
    if dt:
        where.append("substr(%s, 1, 10) <= ?" % col)
        params.append(dt)
    return (" AND ".join(where), params)


def _erp_parse_summary_flavors(items_summary):
    """Best-effort parse of '2x Cheddar, 1x Caramel' into [(qty, name)].

    Skips shipping chunks. Names are kept as-is (variety packs, merch).
    """
    out = []
    for chunk in re.split(r"[;\n]", items_summary or ""):
        for part in chunk.split(","):
            part = part.strip()
            if not part:
                continue
            m = re.match(r"^(\d+)\s*x\s+(.+)$", part, re.IGNORECASE)
            if not m:
                continue
            name = m.group(2).strip()
            if not name or name.lower().startswith("shipping"):
                continue
            try:
                out.append((int(m.group(1)), name[:120]))
            except ValueError:
                pass
    return out


def _erp_csv_response(filename, header, rows):
    import csv
    import io
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(header)
    for r in rows:
        w.writerow(r)
    resp = app.response_class(buf.getvalue(), mimetype="text/csv")
    resp.headers["Content-Disposition"] = "attachment; filename=%s" % filename
    return resp


# ---------- report: sales by flavor/channel ----------

@app.get("/api/erp/reports/sales")
def erp_report_sales():
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    df, dt = _erp_report_dates(request.args)
    if df is None:
        return jsonify(error="from/to must be YYYY-MM-DD"), 400
    channel = (request.args.get("channel") or "all").strip().lower()
    if channel not in ("all", "online", "wholesale"):
        return jsonify(error="channel must be all, online, or wholesale"), 400
    fmt = (request.args.get("format") or "json").strip().lower()
    conn = db()
    where, params = _erp_date_where(df, dt)
    online = {"order_count": 0, "total_cents": 0, "flavors": []}
    wholesale = {"order_count": 0, "total_cents": 0, "flavors": []}
    csv_rows = []
    if channel in ("all", "online"):
        q = ("SELECT id, 'stripe' AS src, email, customer_name, items_summary,"
             " amount_total_cents, total_qty, created_at FROM orders"
             + (" WHERE " + where if where else "")
             + " UNION ALL SELECT id, 'paypal' AS src, email, '' AS customer_name,"
             " items_summary, amount_total_cents, total_qty, created_at"
             " FROM paypal_orders WHERE status = 'captured'"
             + (" AND " + where if where else ""))
        p = params + params
        rows = conn.execute(q, p).fetchall()
        flavors = {}
        for r in rows:
            online["order_count"] += 1
            online["total_cents"] += int(r["amount_total_cents"] or 0)
            for qty, name in _erp_parse_summary_flavors(r["items_summary"]):
                flavors[name] = flavors.get(name, 0) + qty
            if fmt == "csv":
                csv_rows.append(["online", r["src"], "%s-%d" % (r["src"], r["id"]),
                                (r["created_at"] or "")[:10], r["email"] or "",
                                r["items_summary"] or "", r["total_qty"] or 0,
                                r["amount_total_cents"] or 0])
        online["flavors"] = [{"flavor": k, "bags": v}
                             for k, v in sorted(flavors.items(), key=lambda kv: -kv[1])]
    if channel in ("all", "wholesale"):
        q = ("SELECT o.id, o.order_number, o.created_at, a.name AS account_name,"
             " COALESCE(SUM(l.line_total_cents), 0) AS total_cents,"
             " COALESCE(SUM(l.qty_bags), 0) AS bags"
             " FROM erp_wholesale_orders o"
             " JOIN erp_wholesale_accounts a ON a.id = o.account_id"
             " LEFT JOIN erp_wholesale_order_lines l ON l.order_id = o.id"
             + (" WHERE " + where.replace("created_at", "o.created_at") if where else "")
             + " GROUP BY o.id ORDER BY o.id")
        rows = conn.execute(q, params).fetchall()
        flavors = {}
        for r in rows:
            wholesale["order_count"] += 1
            wholesale["total_cents"] += int(r["total_cents"] or 0)
            for ln in conn.execute(
                    "SELECT flavor_name, qty_bags, line_total_cents"
                    " FROM erp_wholesale_order_lines WHERE order_id = ?",
                    (r["id"],)).fetchall():
                f = flavors.setdefault(ln["flavor_name"], {"bags": 0, "total_cents": 0})
                f["bags"] += float(ln["qty_bags"] or 0)
                f["total_cents"] += int(ln["line_total_cents"] or 0)
            if fmt == "csv":
                csv_rows.append(["wholesale", "wholesale", r["order_number"],
                                (r["created_at"] or "")[:10], r["account_name"] or "",
                                "", r["bags"] or 0, r["total_cents"] or 0])
        wholesale["flavors"] = [{"flavor": k, "bags": v["bags"], "total_cents": v["total_cents"]}
                                for k, v in sorted(flavors.items(), key=lambda kv: -kv[1]["bags"])]
    conn.close()
    if fmt == "csv":
        return _erp_csv_response(
            "erp-sales-%s-%s.csv" % (df or "all", dt or "all"),
            ["channel", "source", "order_ref", "date", "customer",
             "items_summary", "bags", "total_cents"],
            csv_rows)
    return jsonify({
        "from": df, "to": dt, "channel": channel,
        "online": online, "wholesale": wholesale,
        "order_count": online["order_count"] + wholesale["order_count"],
        "total_cents": online["total_cents"] + wholesale["total_cents"],
    })


# ---------- report: inventory valuation ----------

@app.get("/api/erp/reports/inventory-valuation")
def erp_report_inventory_valuation():
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    fmt = (request.args.get("format") or "json").strip().lower()
    conn = db()
    rows = conn.execute(
        "SELECT i.id, i.sku, i.name, i.type, l.code AS location_code,"
        " l.name AS location_name, SUM(s.qty_change) AS on_hand,"
        " i.avg_cost_cents"
        " FROM erp_stock_ledger s"
        " JOIN erp_items i ON i.id = s.item_id"
        " JOIN erp_locations l ON l.id = s.location_id"
        " GROUP BY i.id, l.id HAVING on_hand != 0"
        " ORDER BY i.type, i.name, l.code").fetchall()
    items = []
    total_cents = 0
    for r in rows:
        on_hand = float(r["on_hand"] or 0)
        avg = int(r["avg_cost_cents"] or 0)
        value_cents = int(round(on_hand * avg))
        total_cents += value_cents
        items.append({
            "sku": r["sku"], "name": r["name"], "type": r["type"],
            "location_code": r["location_code"], "location_name": r["location_name"],
            "on_hand": on_hand, "avg_cost_cents": avg, "value_cents": value_cents,
        })
    conn.close()
    if fmt == "csv":
        return _erp_csv_response(
            "erp-inventory-valuation.csv",
            ["sku", "name", "type", "location", "on_hand",
             "avg_cost_cents", "value_cents"],
            [[i["sku"], i["name"], i["type"], i["location_code"],
              i["on_hand"], i["avg_cost_cents"], i["value_cents"]] for i in items])
    return jsonify({"items": items, "total_cents": total_cents,
                    "item_count": len(items)})


# ---------- report: production cost & margin ----------

@app.get("/api/erp/reports/production-margin")
def erp_report_production_margin():
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    fmt = (request.args.get("format") or "json").strip().lower()
    df, dt = _erp_report_dates(request.args)
    if df is None:
        return jsonify(error="from/to must be YYYY-MM-DD"), 400
    where, params = _erp_date_where(df, dt, "b.completed_at")
    conn = db()
    rows = conn.execute(
        "SELECT r.id AS recipe_id, r.name AS flavor, r.batch_size_bags,"
        " COUNT(b.id) AS batches, COALESCE(SUM(b.actual_qty_bags), 0) AS bags,"
        " COALESCE(SUM(b.total_cost_cents), 0) AS cost_cents"
        " FROM erp_production_batches b"
        " JOIN erp_recipes r ON r.id = b.recipe_id"
        " WHERE b.status = 'completed' AND b.actual_qty_bags > 0"
        + (" AND " + where if where else "")
        + " GROUP BY r.id ORDER BY r.name", params).fetchall()
    flavors = []
    for r in rows:
        bags = float(r["bags"] or 0)
        cost_cents = int(r["cost_cents"] or 0)
        cpb = (cost_cents / bags) if bags else 0
        flavors.append({
            "flavor": r["flavor"], "batches": r["batches"],
            "bags_produced": bags,
            "cost_per_bag_cents": round(cpb, 2),
            "retail_price_cents": 800,
            "retail_margin_cents": round(800 - cpb, 2),
            "retail_margin_pct": round((800 - cpb) / 800 * 100, 1) if cpb else 100.0,
            "wholesale_price_cents": 400,
            "wholesale_margin_cents": round(400 - cpb, 2),
            "wholesale_margin_pct": round((400 - cpb) / 400 * 100, 1) if cpb else 100.0,
        })
    conn.close()
    note = ("Wholesale price uses the default $4.00/bag; per-account prices may vary. "
            "Retail is $8.00/bag.")
    if fmt == "csv":
        return _erp_csv_response(
            "erp-production-margin.csv",
            ["flavor", "batches", "bags_produced", "cost_per_bag_cents",
             "retail_price_cents", "retail_margin_cents", "retail_margin_pct",
             "wholesale_price_cents", "wholesale_margin_cents",
             "wholesale_margin_pct"],
            [[f["flavor"], f["batches"], f["bags_produced"],
              f["cost_per_bag_cents"], f["retail_price_cents"],
              f["retail_margin_cents"], f["retail_margin_pct"],
              f["wholesale_price_cents"], f["wholesale_margin_cents"],
              f["wholesale_margin_pct"]] for f in flavors])
    return jsonify({"from": df, "to": dt, "flavors": flavors, "note": note})


# ---------- report: wholesale account performance ----------

@app.get("/api/erp/reports/wholesale-performance")
def erp_report_wholesale_performance():
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    fmt = (request.args.get("format") or "json").strip().lower()
    conn = db()
    rows = conn.execute(
        "SELECT a.id, a.name, a.email, a.phone, a.price_per_bag_cents,"
        " COUNT(DISTINCT o.id) AS order_count,"
        " COALESCE(SUM(l.line_total_cents), 0) AS revenue_cents,"
        " MAX(o.created_at) AS last_order_at"
        " FROM erp_wholesale_accounts a"
        " LEFT JOIN erp_wholesale_orders o ON o.account_id = a.id"
        " LEFT JOIN erp_wholesale_order_lines l ON l.order_id = o.id"
        " GROUP BY a.id ORDER BY revenue_cents DESC").fetchall()
    accounts = []
    for r in rows:
        n = int(r["order_count"] or 0)
        rev = int(r["revenue_cents"] or 0)
        accounts.append({
            "id": r["id"], "name": r["name"], "email": r["email"],
            "phone": r["phone"], "price_per_bag_cents": r["price_per_bag_cents"],
            "order_count": n, "revenue_cents": rev,
            "avg_order_cents": int(round(rev / n)) if n else 0,
            "last_order_at": r["last_order_at"],
        })
    conn.close()
    if fmt == "csv":
        return _erp_csv_response(
            "erp-wholesale-performance.csv",
            ["account", "email", "phone", "price_per_bag_cents",
             "order_count", "revenue_cents", "avg_order_cents",
             "last_order_at"],
            [[a["name"], a["email"], a["phone"], a["price_per_bag_cents"],
              a["order_count"], a["revenue_cents"], a["avg_order_cents"],
              a["last_order_at"] or ""] for a in accounts])
    return jsonify({"accounts": accounts,
                    "total_revenue_cents": sum(a["revenue_cents"] for a in accounts)})


# ---------- sales summaries (weekly online rollups for QuickBooks) ----------

def _erp_build_summary(conn, period_start, period_end):
    """Sums ONLINE (Stripe + captured PayPal) sales in [start, end].
    Wholesale is excluded: it reaches QuickBooks as invoices (no double count)."""
    total_cents = 0
    order_count = 0
    for tbl, extra in (("orders", ""), ("paypal_orders", "AND status = 'captured'")):
        r = conn.execute(
            "SELECT COALESCE(SUM(amount_total_cents), 0) AS t, COUNT(*) AS c"
            " FROM %s WHERE substr(created_at, 1, 10) >= ?"
            " AND substr(created_at, 1, 10) <= ? %s" % (tbl, extra),
            (period_start, period_end)).fetchone()
        total_cents += int(r["t"] or 0)
        order_count += int(r["c"] or 0)
    return total_cents, order_count


@app.get("/api/erp/sales-summaries")
def erp_list_sales_summaries():
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    conn = db()
    rows = conn.execute(
        "SELECT s.*, q.qb_id AS qb_sales_receipt_id FROM erp_sales_summaries s"
        " LEFT JOIN erp_qb_links q ON q.entity_type = 'sales_summary'"
        " AND q.entity_id = s.id AND q.qb_object = 'salesreceipt'"
        " ORDER BY s.period_start DESC").fetchall()
    out = [dict(r) for r in rows]
    conn.close()
    return jsonify({"summaries": out})


@app.post("/api/erp/sales-summaries")
def erp_create_sales_summary():
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    data = request.get_json(force=True, silent=True) or {}
    ps = (data.get("period_start") or "").strip()[:10]
    pe = (data.get("period_end") or "").strip()[:10]
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", ps) or not re.match(r"^\d{4}-\d{2}-\d{2}$", pe):
        return jsonify(error="period_start and period_end (YYYY-MM-DD) are required"), 400
    if pe < ps:
        return jsonify(error="period_end is before period_start"), 400
    conn = db()
    if conn.execute(
            "SELECT 1 FROM erp_sales_summaries"
            " WHERE period_start = ? AND period_end = ? AND channel = 'online'",
            (ps, pe)).fetchone():
        conn.close()
        return jsonify(error="a summary already exists for this period"), 409
    total_cents, order_count = _erp_build_summary(conn, ps, pe)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO erp_sales_summaries (period_start, period_end, channel,"
        " total_cents, order_count, status, created_by, created_at)"
        " VALUES (?, ?, 'online', ?, ?, 'draft', ?, ?)",
        (ps, pe, total_cents, order_count, actor, now))
    sid = cur.lastrowid
    conn.commit()
    row = conn.execute("SELECT * FROM erp_sales_summaries WHERE id = ?", (sid,)).fetchone()
    conn.close()
    return jsonify({"summary": dict(row)}), 201


@app.get("/api/erp/sales-summaries/<int:summary_id>")
def erp_get_sales_summary(summary_id):
    actor, err = _erp_check_perm("reports.read")
    if err:
        return err
    conn = db()
    row = conn.execute("SELECT * FROM erp_sales_summaries WHERE id = ?",
                       (summary_id,)).fetchone()
    if not row:
        conn.close()
        return jsonify(error="summary not found"), 404
    link = conn.execute(
        "SELECT qb_id, pushed_at FROM erp_qb_links WHERE entity_type = 'sales_summary'"
        " AND entity_id = ? AND qb_object = 'salesreceipt'",
        (summary_id,)).fetchone()
    out = dict(row)
    out["qb_sales_receipt_id"] = link["qb_id"] if link else None
    out["qb_pushed_at"] = link["pushed_at"] if link else None
    conn.close()
    return jsonify({"summary": out})


# ================= QuickBooks bridge =================
# Backend-held Intuit OAuth + QBO REST v3. The local quickbooks CLI is NOT
# available to this backend; all calls go through _QBOClient below.
# Invoices have no draft state in QuickBooks: every push is preview-first
# and idempotent (erp_qb_links UNIQUE guard + pre-checks).

_QB_AUTH_URL = "https://appcenter.intuit.com/connect/oauth2"
_QB_TOKEN_URL = "https://oauth.platform.intuit.com/oauth2/v1/tokens/bearer"
_QB_API_BASE = "https://quickbooks.api.intuit.com/v3/company"

# Test hook: tests assign backend._QBO_TEST_DOUBLE to a fake implementing
# find_customer / create_customer / create_invoice / create_sales_receipt.
# The suite must NEVER make live Intuit calls.
_QBO_TEST_DOUBLE = None


class _QBOError(Exception):
    def __init__(self, message, status=502):
        super().__init__(message)
        self.status = status


class _QBOUnauthorized(_QBOError):
    pass


class _QBOClient:
    """Minimal QBO REST v3 client. `http` is injectable (tests assert no
    real network by injecting a recording fake)."""

    def __init__(self, access_token, realm_id, http=None):
        self.access_token = access_token
        self.realm_id = realm_id
        self.http = http or requests

    def _url(self, path):
        return "%s/%s/%s" % (_QB_API_BASE, self.realm_id, path)

    def _headers(self):
        return {"Authorization": "Bearer " + self.access_token,
                "Accept": "application/json",
                "Content-Type": "application/json"}

    def _call(self, method, path, params=None, payload=None):
        url = self._url(path)
        try:
            if method == "get":
                r = self.http.get(url, headers=self._headers(),
                                  params=params, timeout=25)
            else:
                r = self.http.post(url, headers=self._headers(), params=params,
                                   data=json.dumps(payload or {}), timeout=25)
        except Exception as e:
            raise _QBOError("QuickBooks request failed: %s" % e)
        if r.status_code == 401:
            raise _QBOUnauthorized("QuickBooks token expired")
        if r.status_code >= 400:
            detail = ""
            try:
                errs = (r.json().get("Fault") or {}).get("Error") or []
                detail = (errs[0] or {}).get("Detail", "") if errs else ""
            except Exception:
                detail = ""
            raise _QBOError("QuickBooks error %s: %s"
                            % (r.status_code, detail or r.text[:200]))
        try:
            return r.json()
        except Exception:
            raise _QBOError("QuickBooks returned a non-JSON response")

    def query(self, qbo_query):
        return self._call("get", "query",
                          params={"query": qbo_query, "minorversion": "65"})

    def find_customer(self, display_name):
        safe = (display_name or "").replace("'", "''")
        data = self.query("select * from Customer where DisplayName = '%s'" % safe)
        custs = ((data.get("QueryResponse") or {}).get("Customer") or [])
        return custs[0] if custs else None

    def create_customer(self, display_name, email=""):
        payload = {"DisplayName": display_name}
        if email:
            payload["PrimaryEmailAddr"] = {"Address": email}
        return self._call("post", "customer",
                          params={"minorversion": "65"}, payload=payload).get("Customer") or {}

    def create_invoice(self, payload):
        return self._call("post", "invoice",
                          params={"minorversion": "65"}, payload=payload).get("Invoice") or {}

    def create_sales_receipt(self, payload):
        return self._call("post", "salesreceipt",
                          params={"minorversion": "65"}, payload=payload).get("SalesReceipt") or {}


def _qb_creds():
    return (os.environ.get("QB_CLIENT_ID") or "",
            os.environ.get("QB_CLIENT_SECRET") or "")


def _qb_redirect_uri():
    return (os.environ.get("QB_REDIRECT_URI") or
            "https://popalicious-gift-cards-production.up.railway.app"
            "/api/erp/quickbooks/callback")


def _qb_frontend_url():
    return os.environ.get("QB_FRONTEND_URL") or "https://erp.pop-a-licious.com"


def _qb_state_token(email):
    s = URLSafeTimedSerializer(AUTH_SECRET, salt="popalicious-qb-oauth")
    return s.dumps({"email": email})


def _qb_state_email(state, max_age=600):
    s = URLSafeTimedSerializer(AUTH_SECRET, salt="popalicious-qb-oauth")
    try:
        return s.loads(state, max_age=max_age).get("email")
    except (BadSignature, SignatureExpired):
        return None


def _qb_tokens(conn):
    return conn.execute("SELECT * FROM erp_qb_oauth WHERE id = 1").fetchone()


def _qb_connected(conn):
    if _QBO_TEST_DOUBLE is not None:
        return True
    tok = _qb_tokens(conn)
    return bool(tok and tok["access_token"] and tok["realm_id"])


def _qb_config(conn, key, default=""):
    row = conn.execute("SELECT value FROM erp_qb_config WHERE key = ?", (key,)).fetchone()
    return row["value"] if row else default


def _qb_pushed(conn, entity_type, entity_id, qb_object):
    return conn.execute(
        "SELECT qb_id FROM erp_qb_links WHERE entity_type = ? AND entity_id = ?"
        " AND qb_object = ?", (entity_type, entity_id, qb_object)).fetchone()


def _qb_store_tokens(conn, access_token, refresh_token, expires_in, realm_id,
                     company_name=""):
    now = datetime.now(timezone.utc)
    conn.execute(
        "INSERT OR REPLACE INTO erp_qb_oauth (id, access_token, refresh_token,"
        " expires_at, realm_id, company_name, updated_at)"
        " VALUES (1, ?, ?, ?, ?, ?, ?)",
        (access_token, refresh_token,
         int(now.timestamp()) + int(expires_in or 3600),
         realm_id, company_name, now.isoformat()))
    conn.commit()


def _qb_refresh_tokens(conn):
    tok = _qb_tokens(conn)
    if not tok or not tok["refresh_token"]:
        return False
    cid, csec = _qb_creds()
    try:
        r = requests.post(_QB_TOKEN_URL,
                          data={"grant_type": "refresh_token",
                                "refresh_token": tok["refresh_token"]},
                          auth=(cid, csec), timeout=25)
    except Exception:
        return False
    if r.status_code != 200:
        return False
    try:
        data = r.json()
    except Exception:
        return False
    _qb_store_tokens(conn, data.get("access_token", ""),
                     data.get("refresh_token", tok["refresh_token"]),
                     data.get("expires_in", 3600), tok["realm_id"],
                     tok["company_name"])
    return True


def _qb_call_with_refresh(conn, fn):
    """Runs fn(client), refreshing the OAuth token once on expiry.

    With the test double set, fn runs against the fake and no network
    is touched. Raises _QBOError on failure; never retries a push.
    """
    if _QBO_TEST_DOUBLE is not None:
        return fn(_QBO_TEST_DOUBLE)
    tok = _qb_tokens(conn)
    if not tok or not tok["access_token"]:
        raise _QBOError("QuickBooks not connected", status=400)
    client = _QBOClient(tok["access_token"], tok["realm_id"])
    try:
        return fn(client)
    except _QBOUnauthorized:
        if _qb_refresh_tokens(conn):
            tok = _qb_tokens(conn)
            return fn(_QBOClient(tok["access_token"], tok["realm_id"]))
        conn.execute("UPDATE erp_qb_oauth SET access_token = '' WHERE id = 1")
        conn.commit()
        raise _QBOError("QuickBooks session expired - please reconnect", status=400)


@app.get("/api/erp/quickbooks/status")
def erp_qb_status():
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    cid, csec = _qb_creds()
    conn = db()
    tok = _qb_tokens(conn)
    connected = (_QBO_TEST_DOUBLE is not None
                 or bool(tok and tok["access_token"] and tok["realm_id"]))
    conn.close()
    return jsonify({
        "configured": bool(cid and csec),
        "connected": connected,
        "realm_id": (tok["realm_id"] if tok else "") or "",
        "company_name": (tok["company_name"] if tok else "") or "",
    })


@app.get("/api/erp/quickbooks/connect")
def erp_qb_connect():
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    cid, csec = _qb_creds()
    if not cid or not csec:
        return jsonify(error="QuickBooks is not configured:"
                              " set QB_CLIENT_ID and QB_CLIENT_SECRET"), 400
    params = {
        "client_id": cid,
        "response_type": "code",
        "scope": "com.intuit.quickbooks.accounting",
        "redirect_uri": _qb_redirect_uri(),
        "state": _qb_state_token(actor),
    }
    return jsonify({"authorize_url": _QB_AUTH_URL + "?" + urlencode(params)})


@app.get("/api/erp/quickbooks/callback")
def erp_qb_callback():
    # Browser redirect from Intuit; no Bearer token. The signed `state`
    # binds this callback to the admin who started the flow.
    email = _qb_state_email(request.args.get("state") or "")
    if not email:
        return redirect(_qb_frontend_url() + "/#/settings?qb=error")
    code = request.args.get("code") or ""
    realm_id = request.args.get("realmId") or ""
    if not code or not realm_id:
        return redirect(_qb_frontend_url() + "/#/settings?qb=error")
    cid, csec = _qb_creds()
    try:
        r = requests.post(_QB_TOKEN_URL,
                          data={"grant_type": "authorization_code",
                                "code": code,
                                "redirect_uri": _qb_redirect_uri()},
                          auth=(cid, csec), timeout=25)
        data = r.json() if r.status_code == 200 else {}
    except Exception:
        data = {}
    if not data.get("access_token"):
        return redirect(_qb_frontend_url() + "/#/settings?qb=error")
    conn = db()
    _qb_store_tokens(conn, data.get("access_token", ""),
                     data.get("refresh_token", ""),
                     data.get("expires_in", 3600), realm_id)
    # Best-effort company name for the settings card.
    try:
        info = _QBOClient(data["access_token"], realm_id).query(
            "select * from CompanyInfo")
        name = (((info.get("QueryResponse") or {}).get("CompanyInfo") or [{}])[0]
                .get("CompanyName", ""))
        if name:
            conn.execute("UPDATE erp_qb_oauth SET company_name = ? WHERE id = 1",
                         (name,))
            conn.commit()
    except _QBOError:
        pass
    conn.close()
    return redirect(_qb_frontend_url() + "/#/settings?qb=connected")


@app.post("/api/erp/quickbooks/disconnect")
def erp_qb_disconnect():
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    conn = db()
    conn.execute("DELETE FROM erp_qb_oauth WHERE id = 1")
    conn.commit()
    conn.close()
    return jsonify({"ok": True, "connected": False})


@app.get("/api/erp/quickbooks/config")
def erp_qb_config_get():
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    conn = db()
    out = {k: _qb_config(conn, k) for k in
           ("wholesale_item_id", "wholesale_item_name", "sales_item_id")}
    conn.close()
    return jsonify({"config": out})


@app.post("/api/erp/quickbooks/config")
def erp_qb_config_set():
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    data = request.get_json(force=True, silent=True) or {}
    conn = db()
    for key in ("wholesale_item_id", "wholesale_item_name", "sales_item_id"):
        if key in data:
            conn.execute("INSERT OR REPLACE INTO erp_qb_config (key, value)"
                         " VALUES (?, ?)", (key, str(data[key] or "").strip()))
    conn.commit()
    out = {k: _qb_config(conn, k) for k in
           ("wholesale_item_id", "wholesale_item_name", "sales_item_id")}
    conn.close()
    return jsonify({"config": out})


def _qb_invoice_payload(order, lines, customer_qb_id, item_id):
    qb_lines = []
    for ln in lines:
        qty = float(ln["qty_bags"] or 0)
        unit_dollars = round((int(ln["unit_price_cents"] or 0)) / 100.0, 2)
        qb_lines.append({
            "Amount": round(qty * unit_dollars, 2),
            "DetailType": "SalesItemLineDetail",
            "Description": "%s popcorn (%s bags)" % (
                ln["flavor_name"], _erp_fmt_qty(qty)),
            "SalesItemLineDetail": {
                "ItemRef": {"value": str(item_id)},
                "Qty": qty,
                "UnitPrice": unit_dollars,
            },
        })
    txn_date = (order["order_date"] or "")[:10]
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", txn_date):
        txn_date = datetime.now(timezone.utc).date().isoformat()
    return {
        "CustomerRef": {"value": str(customer_qb_id)},
        "DocNumber": order["order_number"],
        "TxnDate": txn_date,
        "PrivateNote": "Pop-A-Licious ERP wholesale order %s" % order["order_number"],
        "Line": qb_lines,
    }


def _qb_load_wholesale_order(conn, order_id):
    order = conn.execute("SELECT * FROM erp_wholesale_orders WHERE id = ?",
                         (order_id,)).fetchone()
    if not order:
        return None, None, None
    account = conn.execute("SELECT * FROM erp_wholesale_accounts WHERE id = ?",
                           (order["account_id"],)).fetchone()
    lines = conn.execute(
        "SELECT * FROM erp_wholesale_order_lines WHERE order_id = ? ORDER BY id",
        (order_id,)).fetchall()
    return order, account, lines


@app.post("/api/erp/wholesale-orders/<int:order_id>/quickbooks-preview")
def erp_qb_invoice_preview(order_id):
    """No side effects: shows exactly what a push would send."""
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    conn = db()
    order, account, lines = _qb_load_wholesale_order(conn, order_id)
    if not order:
        conn.close()
        return jsonify(error="order not found"), 404
    if _qb_pushed(conn, "wholesale_order", order_id, "invoice"):
        conn.close()
        return jsonify(error="already pushed to QuickBooks"), 409
    if not _qb_connected(conn):
        conn.close()
        return jsonify(error="QuickBooks not connected"), 400
    if not lines:
        conn.close()
        return jsonify(error="order has no lines"), 400
    item_id = _qb_config(conn, "wholesale_item_id")
    try:
        customer = _qb_call_with_refresh(
            conn, lambda c: c.find_customer(account["name"]))
    except _QBOError as e:
        conn.close()
        return jsonify(error=str(e)), e.status
    total_cents = sum(int(ln["line_total_cents"] or 0) for ln in lines)
    preview = {
        "order_id": order_id,
        "order_number": order["order_number"],
        "customer": {
            "name": account["name"],
            "email": account["email"] or "",
            "qb_id": (customer or {}).get("Id"),
            "will_create": customer is None,
        },
        "lines": [{"flavor": ln["flavor_name"], "qty_bags": ln["qty_bags"],
                   "unit_price_cents": ln["unit_price_cents"],
                   "line_total_cents": ln["line_total_cents"]} for ln in lines],
        "total_cents": total_cents,
        "item_configured": bool(item_id),
        "item_id": item_id or None,
        "item_name": _qb_config(conn, "wholesale_item_name") or None,
    }
    conn.close()
    return jsonify(preview)


@app.post("/api/erp/wholesale-orders/<int:order_id>/quickbooks-push")
def erp_qb_invoice_push(order_id):
    """Creates the QuickBooks invoice. Idempotent: second push -> 409."""
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    conn = db()
    order, account, lines = _qb_load_wholesale_order(conn, order_id)
    if not order:
        conn.close()
        return jsonify(error="order not found"), 404
    if _qb_pushed(conn, "wholesale_order", order_id, "invoice"):
        conn.close()
        return jsonify(error="already pushed to QuickBooks"), 409
    if not _qb_connected(conn):
        conn.close()
        return jsonify(error="QuickBooks not connected"), 400
    if not lines:
        conn.close()
        return jsonify(error="order has no lines"), 400
    item_id = _qb_config(conn, "wholesale_item_id")
    if not item_id:
        conn.close()
        return jsonify(error="configure the QuickBooks wholesale item first"), 400
    try:
        def do_push(client):
            customer = client.find_customer(account["name"])
            if not customer:
                customer = client.create_customer(account["name"],
                                                 account["email"] or "")
                if not customer.get("Id"):
                    raise _QBOError("QuickBooks did not return a customer id")
            payload = _qb_invoice_payload(order, lines, customer["Id"], item_id)
            invoice = client.create_invoice(payload)
            if not invoice.get("Id"):
                raise _QBOError("QuickBooks did not return an invoice id")
            return customer, invoice
        customer, invoice = _qb_call_with_refresh(conn, do_push)
    except _QBOError as e:
        conn.close()
        return jsonify(error=str(e)), e.status
    now = datetime.now(timezone.utc).isoformat()
    try:
        conn.execute(
            "INSERT INTO erp_qb_links (entity_type, entity_id, qb_object,"
            " qb_id, pushed_at, pushed_by)"
            " VALUES ('wholesale_order', ?, 'invoice', ?, ?, ?)",
            (order_id, str(invoice["Id"]), now, actor))
        conn.execute(
            "INSERT OR IGNORE INTO erp_qb_links (entity_type, entity_id,"
            " qb_object, qb_id, pushed_at, pushed_by)"
            " VALUES ('wholesale_account', ?, 'customer', ?, ?, ?)",
            (account["id"], str(customer["Id"]), now, actor))
        conn.commit()
    except sqlite3.IntegrityError:
        conn.rollback()
        conn.close()
        return jsonify(error="already pushed to QuickBooks"), 409
    conn.close()
    return jsonify({"ok": True, "qb_invoice_id": str(invoice["Id"])}), 201


def _qb_receipt_payload(summary, item_id):
    total_dollars = round(int(summary["total_cents"] or 0) / 100.0, 2)
    return {
        "PrivateNote": "Pop-A-Licious ERP online sales summary %s to %s"
                       % (summary["period_start"], summary["period_end"]),
        "Line": [{
            "Amount": total_dollars,
            "DetailType": "SalesItemLineDetail",
            "Description": "Online store sales %s to %s (%d orders)" % (
                summary["period_start"], summary["period_end"],
                int(summary["order_count"] or 0)),
            "SalesItemLineDetail": {"ItemRef": {"value": str(item_id)}},
        }],
    }


@app.post("/api/erp/sales-summaries/<int:summary_id>/quickbooks-preview")
def erp_qb_receipt_preview(summary_id):
    """No side effects: shows exactly what a push would send."""
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    conn = db()
    summary = conn.execute("SELECT * FROM erp_sales_summaries WHERE id = ?",
                           (summary_id,)).fetchone()
    if not summary:
        conn.close()
        return jsonify(error="summary not found"), 404
    if _qb_pushed(conn, "sales_summary", summary_id, "salesreceipt"):
        conn.close()
        return jsonify(error="already pushed to QuickBooks"), 409
    if not _qb_connected(conn):
        conn.close()
        return jsonify(error="QuickBooks not connected"), 400
    item_id = _qb_config(conn, "sales_item_id") or _qb_config(conn, "wholesale_item_id")
    preview = {
        "summary_id": summary_id,
        "period_start": summary["period_start"],
        "period_end": summary["period_end"],
        "channel": summary["channel"],
        "order_count": summary["order_count"],
        "total_cents": summary["total_cents"],
        "item_configured": bool(item_id),
        "item_id": item_id or None,
    }
    conn.close()
    return jsonify(preview)


@app.post("/api/erp/sales-summaries/<int:summary_id>/quickbooks-push")
def erp_qb_receipt_push(summary_id):
    """Creates the QuickBooks sales receipt. Idempotent: second push -> 409."""
    actor, err = _erp_check_perm("qb.manage")
    if err:
        return err
    conn = db()
    summary = conn.execute("SELECT * FROM erp_sales_summaries WHERE id = ?",
                           (summary_id,)).fetchone()
    if not summary:
        conn.close()
        return jsonify(error="summary not found"), 404
    if _qb_pushed(conn, "sales_summary", summary_id, "salesreceipt"):
        conn.close()
        return jsonify(error="already pushed to QuickBooks"), 409
    if not _qb_connected(conn):
        conn.close()
        return jsonify(error="QuickBooks not connected"), 400
    item_id = _qb_config(conn, "sales_item_id") or _qb_config(conn, "wholesale_item_id")
    if not item_id:
        conn.close()
        return jsonify(error="configure the QuickBooks sales item first"), 400
    try:
        payload = _qb_receipt_payload(summary, item_id)
        receipt = _qb_call_with_refresh(conn, lambda c: c.create_sales_receipt(payload))
        if not receipt.get("Id"):
            raise _QBOError("QuickBooks did not return a sales receipt id")
    except _QBOError as e:
        conn.close()
        return jsonify(error=str(e)), e.status
    now = datetime.now(timezone.utc).isoformat()
    try:
        conn.execute(
            "INSERT INTO erp_qb_links (entity_type, entity_id, qb_object,"
            " qb_id, pushed_at, pushed_by)"
            " VALUES ('sales_summary', ?, 'salesreceipt', ?, ?, ?)",
            (summary_id, str(receipt["Id"]), now, actor))
        conn.execute("UPDATE erp_sales_summaries SET status = 'pushed' WHERE id = ?",
                     (summary_id,))
        conn.commit()
    except sqlite3.IntegrityError:
        conn.rollback()
        conn.close()
        return jsonify(error="already pushed to QuickBooks"), 409
    conn.close()
    return jsonify({"ok": True, "qb_sales_receipt_id": str(receipt["Id"])}), 201

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8000)))
