// Commit counts to lalalune/ArkLib main, identities deduped by email.
// Updated 2026-06-30 (15,065 total commits on main).
const lead = {
  user: "lalalune",
  name: "Shaw (lalalune)",
  commits: 10219,
  note: "campaign lead",
};

// Everyone else, equal weight, with commit counts shown.
const campaign: { user: string; name?: string; commits: number }[] = [
  { user: "0xSolace", name: "Sol (0xSolace)", commits: 1715 },
  { user: "lewistham9x", name: "lekt9", commits: 254 },
  { user: "NubsCarson", name: "NubsCarson", commits: 209 },
  { user: "wakesync", name: "wakesync", commits: 154 },
  { user: "2-A-M", name: "2AM", commits: 19 },
  { user: "standujar", name: "Stan", commits: 3 },
];

const foundation: { user: string; name?: string }[] = [
  { user: "quangvdao" },
  { user: "alexanderlhicks", name: "Alexander Hicks" },
  { user: "ElijahVlasov" },
  { user: "katyhr" },
  { user: "Ferinko" },
  { user: "Julek" },
];

function Avatar({
  user,
  name,
  note,
  commits,
  size = 40,
}: {
  user: string;
  name?: string;
  note?: string;
  commits?: number;
  size?: number;
}) {
  return (
    <a
      href={`https://github.com/${user}`}
      className="contrib"
      title={note ?? name ?? user}
    >
      <img
        src={`https://github.com/${user}.png?size=120`}
        alt={`${name ?? user} on GitHub`}
        width={size}
        height={size}
        loading="lazy"
      />
      <span className="mono contrib-name">{name ?? user}</span>
      {typeof commits === "number" ? (
        <span
          className="mono"
          style={{ fontSize: "0.72rem", color: "var(--ink-faint)" }}
        >
          {commits.toLocaleString()}
          {commits >= 1000 ? "+" : ""} commits
        </span>
      ) : null}
    </a>
  );
}

export function Contributors() {
  return (
    <section id="contributors" className="prose-col mt-20">
      <h2 className="text-[1.45rem] font-semibold mb-6">
        The humans and the machines
      </h2>
      <p
        className="text-[0.95rem]"
        style={{ color: "var(--ink-secondary)" }}
      >
        The theorems in this work were produced by a fleet of LLM agents and
        certified by the Lean&nbsp;4 kernel. The people and agents below steered
        the campaign, contributed and reviewed the formalization, and built the
        upstream library it rests on. Authorship is recorded by commit; the
        kernel, not any author, is the arbiter of what is proven.
      </p>

      <h3 className="sc-label text-[0.85rem] font-semibold mt-8 mb-3">
        Campaign &middot;{" "}
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>
      </h3>
      <div className="contrib-grid" style={{ marginBottom: "1.25rem" }}>
        <Avatar {...lead} size={72} />
      </div>
      <div className="contrib-grid">
        {campaign.map((c) => (
          <Avatar key={c.user} {...c} />
        ))}
      </div>

      <h3 className="sc-label text-[0.85rem] font-semibold mt-10 mb-3">
        Foundation &middot; built on{" "}
        <a href="https://github.com/Verified-zkEVM/ArkLib">
          Verified-zkEVM/ArkLib
        </a>
      </h3>
      <p
        className="text-[0.9rem] mb-4"
        style={{ color: "var(--ink-secondary)" }}
      >
        The campaign is a fork. Everything here composes against the formal
        foundation laid by the upstream ArkLib team:
      </p>
      <div className="contrib-grid">
        {foundation.map((c) => (
          <Avatar key={c.user} {...c} />
        ))}
      </div>
    </section>
  );
}
