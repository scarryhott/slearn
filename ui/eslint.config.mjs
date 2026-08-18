import globals from "globals";
import tseslint from "typescript-eslint";

export default tseslint.config(
  { ignores: [".next/**", ".vinext/**", ".wrangler/**", "dist/**", "node_modules/**"] },
  {
    files: ["**/*.{ts,tsx}"],
    extends: [...tseslint.configs.recommended],
    languageOptions: { globals: globals.browser },
  },
);
