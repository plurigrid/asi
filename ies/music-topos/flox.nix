{
  description = "Music Topos: Category Theory in Sound (Overtone)";

  inputs = {
    flox.url = "github:flox/flox";
  };

  outputs = { self, flox }: {
    packages = flox.mkEnvironment {
      buildInputs = [
        # Audio synthesis
        supercollider           # SuperCollider audio synthesis

        # Clojure/JVM
        clojure                 # Clojure language
        leiningen               # Leiningen (Clojure build tool)
        jdk                     # Java Development Kit

        # Utilities
        git
      ];

      shellHook = ''
        echo "🎵 Music Topos Environment (Flox)"
        echo "────────────────────────────────"
        echo ""
        echo "Quick start:"
        echo "  lein run initial    # Play initial object world"
        echo "  lein run terminal   # Play terminal object world"
        echo ""
        echo "REPL:"
        echo "  lein repl"
        echo "  (use 'music-topos.core)"
        echo "  (play-initial-world)"
        echo ""
      '';
    };
  };
}
