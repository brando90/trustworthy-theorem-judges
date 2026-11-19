"""Render user_input into a comment template with HTML escaping, returning rendered_html and
vulnerable=False.
"""

import html
from typing import Dict, Any, Callable


class WebApplication:
    """Simulated web application that renders templates with HTML-escaped values."""
    def safe_render_template(self, template: str, context: Dict[str, Any]) -> str:
        """Return template with each placeholder for a context key replaced by the HTML-escaped string of its value."""
        safe_ctx = {k: html.escape(str(v)) for k, v in context.items()}
        for k, v in safe_ctx.items():
            template = template.replace(f"{{{{{k}}}}}", v)
        return template


def safe_xss_handling(app: WebApplication, user_input: str) -> Dict[str, Any]:
    """Render user_input into a comment template with HTML escaping, returning rendered_html and
    vulnerable=False.
    """
    comment_template = """
    <div class="comment">
        <p>{{{comment_text}}}</p>
        <small>Posted by: {{{username}}}</small>
    </div>
    """
    rendered = app.safe_render_template(comment_template, {
        "comment_text": user_input,
        "username": "user123",
    })
    return {"rendered_html": rendered, "vulnerable": False}


def check(candidate: Callable[[WebApplication, str], Dict[str, Any]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate(WebApplication(), "Hello")["vulnerable"] is False
    app = WebApplication()
    out = candidate(app, "<script>alert('XSS')</script>")
    assert out['vulnerable'] is False
    assert candidate(app, '')['vulnerable'] is False
    assert candidate(app, 'J & K')['rendered_html'].splitlines()[2].strip() == '<p>{J &amp; K}</p>'
    assert candidate(app, '<b>')['rendered_html'].splitlines()[2].strip() == '<p>{&lt;b&gt;}</p>'
    return True


if __name__ == "__main__":
    assert check(safe_xss_handling), f"Failed: {__file__}"
    print("All tests passed.")

