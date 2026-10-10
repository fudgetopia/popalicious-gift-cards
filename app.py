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
from datetime import datetime, timezone

import requests
import stripe
from flask import Flask, jsonify, request
from flask_cors import CORS

# ---------------------------------------------------------------- config

STRIPE_SECRET_KEY = os.environ["STRIPE_SECRET_KEY"]
STRIPE_WEBHOOK_SECRET = os.environ["STRIPE_WEBHOOK_SECRET"]
RESEND_API_KEY = os.environ["RESEND_API_KEY"]
CORS_ORIGINS = os.environ.get("CORS_ORIGINS", "*")
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

stripe.api_key = STRIPE_SECRET_KEY

app = Flask(__name__)
_cors_origins = "*" if CORS_ORIGINS.strip() == "*" else [o.strip() for o in CORS_ORIGINS.split(",") if o.strip()]
CORS(app, origins=_cors_origins)

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
            items_summary TEXT,
            amount_total_cents INTEGER,
            gift_card_code TEXT,
            gift_card_discount_cents INTEGER,
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
            amount_total_cents INTEGER,
            status TEXT NOT NULL,
            created_at TEXT NOT NULL
        );
        """
    )
    conn.commit()
    conn.close()

init_db()

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

# ---------------------------------------------------------------- routes

@app.get("/healthz")
def healthz():
    return jsonify(ok=True)

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

    if not (MIN_AMOUNT_CENTS <= amount <= MAX_AMOUNT_CENTS):
        return jsonify(error=f"amount must be between ${MIN_AMOUNT_CENTS//100} and ${MAX_AMOUNT_CENTS//100}"), 400
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
            success_url=f"{SITE_URL}/gift-card-success?session_id={{CHECKOUT_SESSION_ID}}",
            cancel_url=f"{SITE_URL}/gift-cards",
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
           (stripe_session_id, email, items_summary, amount_total_cents,
            gift_card_code, gift_card_discount_cents, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?)""",
        (session_id, email, items_summary, amount_total, code, discount, now),
    )
    conn.commit()
    conn.close()

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
        return jsonify(error="could not reach the shipping service"), 502

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
    if not options:
        return jsonify(error="no shipping rates found"), 502
    options.sort(key=lambda o: o["amount_cents"])
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
        session = stripe.checkout.Session.create(
            mode="payment",
            line_items=line_items,
            discounts=discounts,
            # A backend-applied discount means the Stripe promo-code box stays off
            # so discounts can never be combined.
            allow_promotion_codes=not (order["gift_card_code"] or order["promo_code"]),
            customer_email=order["email"] or None,
            shipping_address_collection={"allowed_countries": ["US"]},
            phone_number_collection={"enabled": True},
            metadata={
                "type": "order",
                "items_summary": order["summary"],
                "gift_card_code": order["gift_card_code"],
                "gift_card_discount_cents": str(order["gift_card_discount_cents"]),
                "promo_code": order["promo_code"],
            },
            success_url=f"{SITE_URL}/order-success?session_id={{CHECKOUT_SESSION_ID}}",
            cancel_url=f"{SITE_URL}/",
        )
    except stripe.error.StripeError:
        return jsonify(error="the payment service could not start checkout"), 502
    return jsonify(url=session.url, gift_card_discount_cents=order["gift_card_discount_cents"])

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
            gift_card_discount_cents, promo_code, amount_total_cents, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (
            pp["id"], order["email"], order["summary"], order["gift_card_code"],
            order["gift_card_discount_cents"], order["promo_code"], grand,
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

    conn.execute("UPDATE paypal_orders SET status = 'captured' WHERE paypal_order_id = ?", (order_id,))
    conn.execute(
        """INSERT INTO orders
           (stripe_session_id, email, items_summary, amount_total_cents,
            gift_card_code, gift_card_discount_cents, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?)""",
        (f"paypal:{order_id}", email, row["items_summary"], row["amount_total_cents"], code, discount, now),
    )
    conn.commit()
    conn.close()
    return jsonify(ok=True)


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8000)))
