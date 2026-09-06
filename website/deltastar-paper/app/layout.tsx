import type { Metadata } from "next";
import "./globals.css";

const title = "Proximity Prize — research and open problems";
const description = "Formal proofs, exact computations, and open work on Reed–Solomon codes. The prize conjecture remains open.";

export const metadata: Metadata = {
  metadataBase: new URL("https://proximityprize.pages.dev"),
  title, description,
  alternates: { canonical: "/" },
  openGraph: { title, description, type: "website", url: "/", siteName: "Proximity Prize" },
  twitter: { card: "summary", title, description },
};

export default function RootLayout({ children }: Readonly<{ children: React.ReactNode }>) {
  return <html lang="en"><body><a className="skip" href="#main">Skip to content</a>{children}</body></html>;
}
