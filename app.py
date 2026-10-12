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

import os
import re
import secrets
import sqlite3
import string
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
    # Migration: richer order details for the admin order view.
    ocols = [r["name"] for r in conn.execute("PRAGMA table_info(orders)").fetchall()]
    for col in ("customer_name", "shipping_address", "promo_code", "reward_code"):
        if col not in ocols:
            conn.execute(f"ALTER TABLE orders ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
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
        CREATE TABLE IF NOT EXISTS subscription_email_templates (
            name TEXT PRIMARY KEY,
            subject TEXT NOT NULL DEFAULT '',
            body_html TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL DEFAULT ''
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

def send_email(to_email, subject, html):
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
                              discount_cents, promo_code="", shipping=""):
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
    body = "".join(f"<p><strong>{k}:</strong> {v}</p>" for k, v in rows)
    return (
        '<html><body style="font-family: Arial, sans-serif; line-height: 1.6;">'
        "<h2>New Pop-A-Licious order</h2>"
        f"{body}</body></html>"
    )

def notify_merchant_of_order(order_ref, name, email, items_summary,
                             amount_total_cents, gift_card_code,
                             discount_cents, promo_code="", shipping=""):
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
                                      discount_cents, promo_code, shipping),
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
        row = conn.execute(
            "SELECT balance_cents FROM gift_cards WHERE code = ?", (code,)
        ).fetchone()
        if row and row["balance_cents"] >= discount:
            new_bal = row["balance_cents"] - discount
            now = datetime.now(timezone.utc).isoformat()
            conn.execute("UPDATE gift_cards SET balance_cents = ? WHERE code = ?", (new_bal, code))
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
    conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (session_id, email, name, shipping_address, items_summary, amount_total,
         code, discount, promo, rcode, now),
    )
    # Loyalty: mark a redeemed reward code as used (single use).
    if rcode:
        conn.execute(
            "UPDATE loyalty_rewards SET used = 1, used_at = ? WHERE code = ? AND used = 0",
            (now, rcode),
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
                             amount_total, code, discount, promo, shipping)

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
    if row["balance_cents"] < amount:
        conn.close()
        return jsonify(error="insufficient balance", balance_cents=row["balance_cents"]), 402

    new_balance = row["balance_cents"] - amount
    now = datetime.now(timezone.utc).isoformat()
    conn.execute("UPDATE gift_cards SET balance_cents = ? WHERE code = ?", (new_balance, code))
    conn.execute(
        "INSERT INTO redemptions (code, amount_cents, order_ref, created_at) VALUES (?, ?, ?, ?)",
        (code, amount, order_ref, now),
    )
    conn.commit()
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
    conn.close()
    if not row or not row["active"]:
        return jsonify(error="code not found"), 404
    return jsonify(type="gift_card", code=code, balance_cents=row["balance_cents"])

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
    except (TypeError, ValueError):
        return None, (jsonify(error="invalid shipping"), 400)
    shipping_label = (data.get("shipping_label") or "").strip()[:120]
    if shipping_cents < 0 or shipping_cents > 100000:
        return None, (jsonify(error="invalid shipping"), 400)

    order = {
        "items": items,
        "merchandise_total": total,
        "email": email,
        "shipping_cents": shipping_cents,
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

    discounts = []
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
            gift_card_discount_cents, promo_code, reward_code, amount_total_cents, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (
            pp["id"], order["email"], order["summary"], order["gift_card_code"],
            order["gift_card_discount_cents"], order["promo_code"], order["reward_code"], grand,
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
        gc = conn.execute(
            "SELECT balance_cents FROM gift_cards WHERE code = ?", (code,)
        ).fetchone()
        if gc and gc["balance_cents"] >= discount:
            conn.execute(
                "UPDATE gift_cards SET balance_cents = ? WHERE code = ?",
                (gc["balance_cents"] - discount, code),
            )
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
    notify_merchant_of_order(order_id, name, email, row["items_summary"],
                             row["amount_total_cents"], code, discount,
                             promo, shipping)

    conn.execute("UPDATE paypal_orders SET status = 'captured' WHERE paypal_order_id = ?", (order_id,))
    prcode = row["reward_code"] or ""
    conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (f"paypal:{order_id}", email, name, shipping, row["items_summary"],
         row["amount_total_cents"], code, discount, promo, prcode, now),
    )
    # Loyalty: mark a redeemed reward code as used (single use).
    rcode = prcode
    if rcode:
        conn.execute(
            "UPDATE loyalty_rewards SET used = 1, used_at = ? WHERE code = ? AND used = 0",
            (now, rcode),
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
        "SELECT id, name FROM users WHERE email = ?", (email,)
    ).fetchone()
    if row:
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
    if not row["verified"]:
        return jsonify(
            error="please verify your email before logging in — check your inbox",
            needs_verification=True,
        ), 403
    token = _issue_auth_token(row["id"])
    resp = jsonify(name=row["name"], email=row["email"], token=token)
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
            " VALUES (?, '', 1, ?, ?)",
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
    "free_shipping": {"kernels": 25, "label": "Free shipping on one order"},
    "free_bag": {"kernels": 50, "label": "Free single bag"},
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
    "merch_item": {"kernels": 100, "label": "Free merch item", "kind": "merch"},
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

def _debit_kernels(conn, user_id, kernels, reason, order_ref=""):
    if kernels <= 0:
        return False
    if _kernel_balance(conn, user_id) < kernels:
        return False
    conn.execute(
        "INSERT INTO kernel_transactions (user_id, kernels, reason, order_ref, created_at)"
        " VALUES (?, ?, ?, ?, ?)",
        (user_id, -kernels, reason, order_ref,
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
    if month != datetime.now().month:
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
        "SELECT birthday FROM users WHERE id = ?", (user["id"],)
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
    if not conn.execute("SELECT 1 FROM users WHERE id = ?", (user_id,)).fetchone():
        conn.close()
        return jsonify(error="member not found"), 404
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
    if not conn.execute("SELECT 1 FROM users WHERE id = ?", (user_id,)).fetchone():
        conn.close()
        return jsonify(error="member not found"), 404
    code = _new_reward_code()
    if not _debit_kernels(conn, user_id, tier["kernels"], "redemption_in_person",
                          order_ref=code, staff_id=staff["id"]):
        conn.close()
        return jsonify(error="not enough Kernels"), 402
    conn.execute(
        "INSERT INTO loyalty_rewards (user_id, reward_type, code, kernels_spent, created_at)"
        " VALUES (?, ?, ?, ?, ?)",
        (user_id, reward_type, code, tier["kernels"],
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
    conn.close()
    return jsonify(
        id=row["id"], name=row["name"], email=row["email"],
        headshot=row["headshot"] or "", kernels=row["kernels"] or 0,
        birthday=row["birthday"] or "", hire_date=row["hire_date"] or "",
        referral_code=row["referral_code"] or "",
        created_at=row["created_at"],
        reward_tiers={k: v["kernels"] for k, v in STAFF_REWARD_TIERS.items()},
        reward_labels={k: v["label"] for k, v in STAFF_REWARD_TIERS.items()},
        history=[
            {"kernels": h["kernels"], "reason": h["reason"], "ref": h["ref"] or "",
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
            " gift_card_discount_cents, promo_code, reward_code, created_at"
            " FROM orders WHERE id = ?",
            (int(order_id) - 1000,),
        ).fetchone()
    else:
        r = conn.execute(
            "SELECT id, stripe_session_id, email, customer_name, shipping_address,"
            " items_summary, amount_total_cents, gift_card_code,"
            " gift_card_discount_cents, promo_code, reward_code, created_at"
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
        payment_method="PayPal" if r["stripe_session_id"].startswith("paypal:") else "Stripe",
        created_at=r["created_at"],
    )

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
        " o.promo_code, o.reward_code, o.created_at"
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
        recent_orders=[
            {"email": r["email"], "items": r["items_summary"] or "",
             "total_cents": r["amount_total_cents"] or 0, "created_at": r["created_at"]}
            for r in recent_orders
        ],
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
    if not conn.execute(
        "SELECT 1 FROM fundraiser_sellers WHERE id = ?", (seller_id,)
    ).fetchone():
        conn.close()
        return jsonify(error="seller not found"), 404
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
        conn.execute(
            """INSERT INTO fundraiser_orders
               (fundraiser_id, seller_id, order_number, customer_name, customer_email,
                ship_name, ship_street, ship_city, ship_state, ship_zip,
                items, subtotal_cents, donation_cents, roundup_cents,
                shipping_cents, total_cents, stripe_payment_intent_id, status, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'paid', ?)""",
            (fr["id"], seller_id, order_number, customer_name, customer_email,
             (meta.get("ship_name") or "")[:120], (meta.get("ship_street") or "")[:200],
             (meta.get("ship_city") or "")[:120], (meta.get("ship_state") or "")[:2],
             (meta.get("ship_zip") or "")[:10],
             json.dumps(items), subtotal, donation, roundup, ship_cents, total,
             pi_id, now),
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
                             summary, total, "", 0, "", shipping)
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
    """Organizer view (public via code knowledge)."""
    conn = db()
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE id = ?", (fid,)).fetchone()
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

@app.post("/api/fundraisers/<int:fid>/nudge")
def fundraiser_nudge(fid):
    data = request.get_json(force=True) or {}
    try:
        seller_id = int(data.get("seller_id") or 0)
    except (TypeError, ValueError):
        return jsonify(error="seller_id is required"), 400
    conn = db()
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
    conn = db()
    fr = conn.execute(
        "SELECT * FROM fundraisers WHERE id = ?", (fid,)).fetchone()
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
    conn = db()
    if not conn.execute(
        "SELECT 1 FROM fundraisers WHERE id = ?", (fid,)
    ).fetchone():
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
            "UPDATE subscription_renewals SET status = 'failed' WHERE id = ?",
            (renewal["id"],))
        return False, (jsonify(error=_stripe_error_message(e)), 402)
    if pi.get("status") not in ("succeeded", "processing"):
        conn.execute(
            "UPDATE subscription_renewals SET status = 'failed' WHERE id = ?",
            (renewal["id"],))
        return False, (jsonify(error="the payment could not be completed"), 402)

    now = datetime.now(timezone.utc).isoformat()
    summary = _items_summary_str(items)
    ship_addr = ", ".join(
        x for x in [sub["ship_name"], sub["ship_street"], sub["ship_city"],
                    sub["ship_state"], sub["ship_zip"]] if x)
    cur = conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, customer_name, shipping_address, items_summary,
            amount_total_cents, gift_card_code, gift_card_discount_cents,
            promo_code, reward_code, created_at)
           VALUES (?, ?, ?, ?, ?, ?, '', 0, '', '', ?)""",
        (f"sub_{pi.id}", sub["ship_email"] or "", sub["ship_name"] or "",
         ship_addr, summary, amount, now))
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
        "", 0, "", payload["ship_addr"])
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

    # 2) Charges: renewals past their billing date, reminded/confirmed, not charged.
    dues = conn.execute(
        "SELECT id FROM subscription_renewals"
        " WHERE billing_date < ? AND status IN ('reminded', 'confirmed')",
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
                "", 0, "", payload["ship_addr"])
        else:
            failed += 1
    conn.close()
    return jsonify(reminded=reminded, charged=charged, failed=failed)

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


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8000)))
