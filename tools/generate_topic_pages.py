from html import escape
import json
from pathlib import Path
from urllib.parse import quote

BASE_URL = "https://artinnether.github.io/the_mathematical_physics_project/"
ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"

PAPERS = json.loads(Path(__file__).with_name("papers.json").read_text(encoding="utf-8"))

LANGUAGE_NAMES = {"en": "English", "es": "Español"}
LABELS = {
    "en": {
        "locale": "en_US", "navigation": "Site navigation", "latest": "Latest",
        "library": "Library", "subscribe": "Subscribe", "contact": "Contact",
        "read": "Read PDF", "download": "Download PDF", "share": "Share this article",
        "details": "Article details", "topics": "Related topics",
        "pdf_languages": {"en": "English", "es": "Spanish"},
    },
    "es": {
        "locale": "es_MX", "navigation": "Navegación del sitio", "latest": "Publicaciones",
        "library": "Biblioteca", "subscribe": "Suscripción", "contact": "Contacto",
        "read": "Leer PDF", "download": "Descargar PDF", "share": "Compartir este artículo",
        "details": "Detalles del artículo", "topics": "Temas relacionados",
        "pdf_languages": {"en": "inglés", "es": "español"},
    },
}

SITEMAP_PDFS = [
    ("fiber_bundle_construction_of_quantum_electrodynamics.pdf", "2026-11-05", "0.9"),
    ("construccion_electrodinamica_cuantica_mediante_haces_fibrados.pdf", "2026-11-05", "0.9"),
    ('qft_notes_78_80_english.pdf', "2026-09-30", "0.8"),
    ('notas_qft_78_80_con_dibujo_definiciones.pdf', "2026-09-30", "0.8"),
    ("notas_algebras_lie_envolvente_universal.pdf", "2026-09-02", "0.9"),
    ("notes_lie_algebras_universal_enveloping_algebra.pdf", "2026-09-02", "0.9"),
    ("Algebras_C_estrella_y_Notacion_Daga_ES.pdf", "2026-07-16", "0.9"),
    ("C_star_Algebras_and_Dagger_Notation_EN.pdf", "2026-07-16", "0.9"),
    ("Algebra_Homologica_en_la_Categoria_de_Modulos_ES.pdf", "2026-07-06", "0.8"),
    ("Homological_Algebra_in_the_Category_of_Modules_EN.pdf", "2026-07-06", "0.8"),
    ("Feynman_Prescription_Residues_and_Real_Poles_ES.pdf", "2026-06-17", "0.8"),
    ("Feynman_Prescription_Residues_and_Real_Poles_EN.pdf", "2026-06-17", "0.8"),
    ("Expansion_Perturbativa_y_Diagramas_de_Feynman_en_el_Modelo_lambda_phi4_de_Dimension_Cero.pdf", "2026-06-09", "0.8"),
    ("Lorentz_Invariance_of_the_Klein_Gordon_Field_and_Action.pdf", "2026-06-06", "0.8"),
    ("Relacion entre el Vacio Libre, el Vacio Interactuante, Serie de Dyson y las Funciones de Correlacion.pdf", "2026-05-27", "0.7"),
    ("Libro.pdf", "2026-05-09", "0.9"),
    ("Control_Theory_Excercises.pdf", "2026-05-09", "0.6"),
    ("Field Variations on Vector Bundles with Connection A Unified Active and Passive Interpretation.pdf", "2026-05-09", "0.7"),
    ("epsilon-Ecuaciones Hamiltonianas de ADM de la Relatividad General.pdf", "2026-04-23", "0.7"),
    ("The_Brachistochrone_Problem__Time_Minimization_via_Calculus_of_Variations-Corona.pdf", "2026-04-23", "0.7"),
    ("The Einbein.pdf", "2026-04-23", "0.7"),
    ("On_the_Functional_Derivative_of_the_Scalar_Field_Action_and__the_Associated_Global_Functional.pdf", "2026-04-23", "0.7"),
    ("Linear_Algebra_Exercises.pdf", "2026-04-23", "0.6"),
    ("Formulacion Matematica de las Imagenes de Heisenberg, Schrodinger y Dirac.pdf", "2026-04-23", "0.7"),
    ("Forma Heurística de la Ecuación de Dirac.pdf", "2026-04-23", "0.7"),
    ("Fijación_Gauge_en_la_Integral_de_Camino_y_el_Determinante_de_Faddeev_Popov.pdf", "2026-04-23", "0.7"),
    ("El_grupo_SU2_como_grupo_de_Lie_y_Vision_Fisica.pdf", "2026-04-23", "0.7"),
    ("Differential_Equations_Exercises.pdf", "2026-04-23", "0.6"),
    ("Composite_Quantum_Systems_and_Their_Wave_Functions-3.pdf", "2026-04-23", "0.7"),
    ("Calculus_excercises.pdf", "2026-04-23", "0.6"),
]


def enc(path):
    return quote(path, safe="/:")


def paper_path(slug, lang):
    suffix = "-es" if lang == "es" else ""
    return f"papers/{slug}{suffix}.html"


def render_paper(paper, lang):
    labels = LABELS[lang]
    other_lang = "en" if lang == "es" else "es"
    page = paper[lang]
    url = BASE_URL + paper_path(paper["slug"], lang)
    other_path = paper_path(paper["slug"], other_lang)
    other_url = BASE_URL + other_path
    pdfs = paper["pdfs"]
    pdf_lang = lang if lang in pdfs else other_lang
    pdf = enc(pdfs[pdf_lang])
    pdf_language = labels["pdf_languages"][pdf_lang]
    alt_link = ""
    if other_lang in pdfs and other_lang != pdf_lang:
        alt_pdf = enc(pdfs[other_lang])
        alt_language = labels["pdf_languages"][other_lang]
        alt_link = f'        <a href="../{alt_pdf}" class="secondary-action">{labels["read"]} ({alt_language})</a>'

    cover = page["cover"]
    preview_image = enc(cover["file"])
    cover_alt = escape(cover["alt"])
    metadata = {
        "@context": "https://schema.org",
        "@type": "ScholarlyArticle",
        "headline": page["title"],
        "alternativeHeadline": paper[other_lang]["title"],
        "description": page["description"],
        "url": url,
        "image": BASE_URL + preview_image,
        "encoding": {
            "@type": "MediaObject", "contentUrl": BASE_URL + pdf,
            "encodingFormat": "application/pdf", "inLanguage": pdf_lang,
        },
        "author": {"@type": "Person", "name": "Omar Corona Tejeda", "url": BASE_URL},
        "isPartOf": {"@type": "CollectionPage", "name": "The Mathematical Physics Project", "url": BASE_URL},
        "about": page["category"],
        "inLanguage": lang,
    }
    structured_data = json.dumps(metadata, ensure_ascii=False, indent=2).replace("<", "\\u003c")
    share_text = quote(f"{page['title']} - The Mathematical Physics Project")
    share_url = quote(url, safe="")
    topics = "".join(f"<li>{escape(topic.strip())}</li>" for topic in page["keywords"].split(",")[:6])
    topics_panel = ""
    if page["keywords"] != page["title"]:
        topics_panel = f'''    <section class="panel" aria-label="{labels['details']}">
      <h2>{labels['topics']}</h2>
      <ul>{topics}</ul>
    </section>'''

    return f"""<!doctype html>
<html lang="{lang}">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width,initial-scale=1" />
  <title>{escape(page['title'])} | The Mathematical Physics Project</title>
  <meta name="description" content="{escape(page['description'])}" />
  <meta name="keywords" content="{escape(page['keywords'])}" />
  <meta name="author" content="Omar Corona Tejeda" />
  <meta name="robots" content="index, follow, max-image-preview:large" />
  <link rel="canonical" href="{url}" />
  <link rel="alternate" hreflang="{lang}" href="{url}" />
  <link rel="alternate" hreflang="{other_lang}" href="{other_url}" />
  <link rel="icon" href="../tmpp_logo.png" type="image/png" />
  <link rel="apple-touch-icon" href="../tmpp_logo.png" />
  <meta property="og:site_name" content="The Mathematical Physics Project" />
  <meta property="og:title" content="{escape(page['title'])}" />
  <meta property="og:description" content="{escape(page['description'])}" />
  <meta property="og:type" content="article" />
  <meta property="og:locale" content="{labels['locale']}" />
  <meta property="og:locale:alternate" content="{LABELS[other_lang]['locale']}" />
  <meta property="og:url" content="{url}" />
  <meta property="og:image" content="{BASE_URL}{preview_image}" />
  <meta property="og:image:width" content="1200" />
  <meta property="og:image:height" content="630" />
  <meta property="og:image:alt" content="{cover_alt}" />
  <meta name="twitter:card" content="summary_large_image" />
  <meta name="twitter:title" content="{escape(page['title'])}" />
  <meta name="twitter:description" content="{escape(page['description'])}" />
  <meta name="twitter:image" content="{BASE_URL}{preview_image}" />
  <meta name="twitter:image:alt" content="{cover_alt}" />
  <script type="application/ld+json">
{structured_data}
  </script>
  <style>
    :root {{
      --ink: #111827;
      --muted: #526071;
      --brand: #1f2a30;
      --gold: #d8c28a;
      --paper: rgba(255, 255, 255, 0.76);
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      min-height: 100vh;
      color: var(--ink);
      font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      background: url("../fondo.png") center / cover fixed no-repeat;
    }}
    header {{
      background: linear-gradient(180deg, rgba(31,42,48,0.98), rgba(31,42,48,0.90));
      border-bottom: 1px solid rgba(216, 194, 138, 0.45);
      box-shadow: 0 14px 38px rgba(15, 23, 42, 0.20);
    }}
    nav {{
      width: min(1120px, calc(100% - 32px));
      margin: 0 auto;
      min-height: 86px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 20px;
    }}
    .brand {{
      display: flex;
      align-items: center;
      gap: 14px;
      color: white;
      text-decoration: none;
      font-weight: 800;
    }}
    .brand img {{
      width: 48px;
      height: 48px;
      border-radius: 999px;
      border: 2px solid rgba(255,255,255,0.78);
    }}
    .nav-links {{
      display: flex;
      flex-wrap: wrap;
      justify-content: flex-end;
      gap: 16px;
      font-size: 0.95rem;
      font-weight: 700;
    }}
    .nav-links a {{ color: white; text-decoration: none; }}
    .nav-links a:hover {{ text-decoration: underline; }}
    main {{
      width: min(1040px, calc(100% - 32px));
      margin: 0 auto;
      padding: 52px 0 72px;
    }}
    .hero {{
      display: grid;
      gap: 24px;
      padding: 36px;
      border: 1px solid rgba(31, 42, 48, 0.12);
      border-radius: 20px;
      background: var(--paper);
      box-shadow: 0 22px 54px rgba(15, 23, 42, 0.10);
      backdrop-filter: blur(7px);
    }}
    .eyebrow {{
      margin: 0;
      color: #526071;
      font-size: 0.78rem;
      font-weight: 800;
      letter-spacing: 0.18em;
      text-transform: uppercase;
    }}
    h1 {{
      max-width: 860px;
      margin: 0;
      color: var(--ink);
      font-size: clamp(2.1rem, 5vw, 4.4rem);
      line-height: 1.03;
      letter-spacing: 0;
    }}
    .summary {{
      max-width: 820px;
      margin: 0;
      color: var(--muted);
      font-size: 1.16rem;
      line-height: 1.72;
    }}
    .actions, .share {{
      display: flex;
      flex-wrap: wrap;
      gap: 12px;
      align-items: center;
    }}
    .primary-action, .secondary-action, .share a {{
      display: inline-flex;
      align-items: center;
      justify-content: center;
      min-height: 44px;
      padding: 0 16px;
      border-radius: 10px;
      color: white;
      text-decoration: none;
      font-weight: 800;
    }}
    .primary-action {{ background: var(--brand); }}
    .secondary-action {{ background: #475569; }}
    .share a {{ background: #2563eb; }}
    .share a:nth-child(2) {{ background: #111827; }}
    .share a:nth-child(3) {{ background: #16a34a; }}
    .cover {{ margin: 0; max-width: 620px; }}
    .cover img {{ display: block; width: 100%; height: auto; border-radius: 10px; }}
    .cover figcaption {{ margin-top: 8px; color: var(--muted); }}
    .panel {{
      margin-top: 18px;
      padding: 22px;
      border: 1px solid rgba(31, 42, 48, 0.12);
      border-radius: 12px;
      background: rgba(255, 255, 255, 0.66);
    }}
    .panel h2 {{
      margin: 0 0 10px;
      font-size: 1.08rem;
    }}
    .panel p, .panel li {{
      color: var(--muted);
      line-height: 1.62;
    }}
    .panel ul {{
      margin: 0;
      padding-left: 20px;
    }}
    footer {{
      width: min(1040px, calc(100% - 32px));
      margin: 0 auto;
      padding: 0 0 42px;
      color: var(--muted);
      text-align: center;
    }}
    @media (max-width: 760px) {{
      nav {{ align-items: flex-start; flex-direction: column; padding: 18px 0; }}
      .nav-links {{ justify-content: flex-start; }}
      .hero {{ padding: 24px; }}
    }}
  </style>
</head>
<body>
  <header>
    <nav aria-label="{labels['navigation']}">
      <a class="brand" href="../">
        <img src="../tmpp_logo.png" alt="" />
        <span>The Mathematical Physics Project</span>
      </a>
      <div class="nav-links">
        <a href="../#latest">{labels['latest']}</a>
        <a href="../#pdfs">{labels['library']}</a>
        <a href="../#newsletter">{labels['subscribe']}</a>
        <a href="../#contacto">{labels['contact']}</a>
        <a href="../{other_path}" lang="{other_lang}" hreflang="{other_lang}">{LANGUAGE_NAMES[other_lang]}</a>
      </div>
    </nav>
  </header>
  <main>
    <article class="hero">
      <p class="eyebrow">{escape(page['category'])}</p>
      <h1>{escape(page['title'])}</h1>
      <p class="summary">{escape(page['description'])}</p>
      <div class="actions">
        <a href="../{pdf}" class="primary-action" target="_blank" rel="noopener noreferrer">{labels['read']} ({pdf_language})</a>
        <a href="../{pdf}" class="secondary-action" download>{labels['download']}</a>
{alt_link}
      </div>
      <figure class="cover">
        <img src="../{preview_image}" alt="{cover_alt}" width="1200" height="630" />
      </figure>
      <div class="share" aria-label="{labels['share']}">
        <a href="https://www.linkedin.com/sharing/share-offsite/?url={share_url}" target="_blank" rel="noopener noreferrer">LinkedIn</a>
        <a href="https://twitter.com/intent/tweet?url={share_url}&text={share_text}" target="_blank" rel="noopener noreferrer">X</a>
        <a href="https://api.whatsapp.com/send?text={share_text}%20{share_url}" target="_blank" rel="noopener noreferrer">WhatsApp</a>
      </div>
    </article>
{topics_panel}
  </main>
  <footer>
    <p>Omar Corona Tejeda - The Mathematical Physics Project</p>
  </footer>
</body>
</html>
"""


def write_sitemap():
    entries = [
        ("", "2026-06-27", "weekly", "1.0"),
    ]
    entries += [
        (paper_path(paper["slug"], lang), paper["lastmod"], "monthly", "0.9")
        for paper in PAPERS
        for lang in LABELS
    ]
    entries += [(pdf, date, "monthly", priority) for pdf, date, priority in SITEMAP_PDFS]
    body = ['<?xml version="1.0" encoding="UTF-8"?>', '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
    for loc, lastmod, changefreq, priority in entries:
        url = BASE_URL + enc(loc)
        body.extend([
            "  <url>",
            f"    <loc>{url}</loc>",
            f"    <lastmod>{lastmod}</lastmod>",
            f"    <changefreq>{changefreq}</changefreq>",
            f"    <priority>{priority}</priority>",
            "  </url>",
        ])
    body.append("</urlset>")
    (ROOT / "sitemap.xml").write_text("\n".join(body) + "\n", encoding="utf-8")


def main():
    PAPERS_DIR.mkdir(exist_ok=True)
    for paper in PAPERS:
        for lang in LABELS:
            (ROOT / paper_path(paper["slug"], lang)).write_text(render_paper(paper, lang), encoding="utf-8")
    write_sitemap()


if __name__ == "__main__":
    main()

