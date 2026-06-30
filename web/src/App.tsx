import { AppShell } from "./app-shell";
import { useAppModel } from "./app-model";

export function App() {
  const model = useAppModel();
  return <AppShell model={model} />;
}
