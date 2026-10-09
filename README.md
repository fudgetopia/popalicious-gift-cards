# Pop-A-Licious Gift Card Backend

Small service that powers the gift card flow on pop-a-licious.com:

1. Site's gift card form → `POST /api/gift-cards/checkout` → customer pays with Stripe Checkout
2. Stripe webhook → service issues a unique code (e.g. `PAL-X7Q2-9M4D`), stores it, and emails
   the recipient your gift card message with the names and code auto-filled
3. `GET /api/gift-cards/balance?code=...` powers the balance-check page
4. `POST /api/gift-cards/redeem` deducts an amount when a code is used at checkout

## What you need (all free to start)

1. **Stripe secret key** — Dashboard → Developers → API keys → "Create restricted key".
   Give it write access to Checkout Sessions and read access to Products/Prices.
   (Never put this key in the website's frontend code — it lives only on this server.)
2. **Resend account** (resend.com) for the automatic recipient emails → API key.
   Verify your sending domain in Resend, or test with their onboarding address first.
3. **Hosting** — Railway (railway.app) or Render (render.com). Both deploy this Dockerfile
   in a few clicks and give you a public `https://...` URL.

## Deploy

1. Push this folder to a Git repo (or deploy the Dockerfile directly).
2. On Railway/Render: New project → deploy from repo → set these env vars:
   `STRIPE_SECRET_KEY`, `STRIPE_WEBHOOK_SECRET` (step 4), `RESEND_API_KEY`,
   `EMAIL_FROM`, `SITE_URL` (your live site URL), `GIFT_CARD_PRODUCT_ID`.
3. Note the public URL, e.g. `https://popalicious-gifts.up.railway.app`.

## Stripe webhook

1. Dashboard → Developers → Webhooks → Add endpoint:
   `https://<your-backend>/api/webhooks/stripe`
2. Select event `checkout.session.completed` → Add endpoint.
3. Copy the **Signing secret** (`whsec_...`) → set as `STRIPE_WEBHOOK_SECRET` env var → redeploy.

## Website integration (gift card form)

Replace the gift card form's submit with:

```js
const res = await fetch("https://<your-backend>/api/gift-cards/checkout", {
  method: "POST",
  headers: { "Content-Type": "application/json" },
  body: JSON.stringify({
    amount_cents: 2500,               // $25.00
    purchaser_name: "...",
    purchaser_email: "...",
    recipient_name: "...",
    recipient_email: "...",
    message: "...",                   // optional
    non_refundable_ack: true          // checkbox, required
  })
});
const { url, error } = await res.json();
if (error) { /* show error */ } else { window.location = url; }  // Stripe Checkout
```

Balance check page:

```js
const res = await fetch(`https://<your-backend>/api/gift-cards/balance?code=${encodeURIComponent(code)}`);
```

Redeem at site checkout (call after the order's payment succeeds):

```js
await fetch("https://<your-backend>/api/gift-cards/redeem", {
  method: "POST",
  headers: { "Content-Type": "application/json" },
  body: JSON.stringify({ code, amount_cents, order_ref: "order-123" })
});
```

## Notes

- SQLite is used for simplicity; point `DATABASE_PATH` at persistent storage on your host
  (Railway/Render volumes) so codes survive redeploys. Move to Postgres when volume grows.
- Webhook fulfillment is idempotent: retried Stripe events won't double-issue codes.
- Test the whole flow with a Stripe **test-mode** key and `https://` tunnel before going live.
