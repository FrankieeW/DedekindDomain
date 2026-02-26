from invoke import task


@task
def web(c):
    c.run("leanblueprint web", pty=True)


@task
def bp(c):
    c.run("leanblueprint pdf", pty=True)


@task
def serve(c, port=8080):
    c.run(f"python -m http.server {port} -d web", pty=True)
