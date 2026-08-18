import type { Metadata } from "next";
import { headers } from "next/headers";
import "./globals.css";

export async function generateMetadata(): Promise<Metadata> {
  const requestHeaders = await headers();
  const host = requestHeaders.get("host") ?? "localhost:3001";
  const protocol = requestHeaders.get("x-forwarded-proto") ?? "https";
  const image = `${protocol}://${host}/og.png`;

  return {
    title: "Slearn · Perspectival Closure Map",
    description:
      "A generated Slearn map: perspective, value and belief, WHY/reason, goal, lesson, project, and returned world relation.",
    openGraph: {
      title: "Slearn · Perspectival Closure Map",
      description:
        "Perspective and goal recenter one maintained translation through witnessed reasons, attempts, and return receipts.",
      images: [{ url: image, width: 1536, height: 1024, alt: "Slearn Closure Runtime" }],
    },
    twitter: {
      card: "summary_large_image",
      title: "Slearn · Perspectival Closure Map",
      description:
        "Perspective and goal recenter one maintained translation through witnessed reasons, attempts, and return receipts.",
      images: [image],
    },
  };
}

export default function RootLayout({ children }: Readonly<{ children: React.ReactNode }>) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
