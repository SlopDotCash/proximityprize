const token = process.env.CLOUDFLARE_API_TOKEN;
const account = process.env.CLOUDFLARE_ACCOUNT_ID;
if (!token || !account) throw new Error("Configure PROXIMITYPRIZE_CLOUDFLARE_API_TOKEN and PROXIMITYPRIZE_CLOUDFLARE_ACCOUNT_ID before deploying.");
const response = await fetch(`https://api.cloudflare.com/client/v4/accounts/${account}/pages/projects/proximityprize`, {
  headers: { Authorization: `Bearer ${token}` }, signal: AbortSignal.timeout(20000),
});
const body = await response.json();
if (!response.ok || !body.success || body.result?.production_branch !== "main" || body.result?.subdomain !== "proximityprize.pages.dev") {
  throw new Error("Cloudflare access or project mismatch: expected proximityprize.pages.dev with production branch main in the configured account.");
}
console.log("Confirmed proximityprize.pages.dev, production branch main.");
