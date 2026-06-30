import { expect, test } from "@playwright/test";

import {
  publishFundingFeeRate,
  publishParticipantAnnouncement,
  publishVote,
} from "../src/lib/lwk/publishing";

test("multisig creation descriptor can be moved between isolated browser sessions", async ({
  browser,
}) => {
  const creatorContext = await browser.newContext();
  const loaderContext = await browser.newContext();

  try {
    const creatorPage = await creatorContext.newPage();
    await creatorPage.goto("/");
    await expect(creatorPage).toHaveTitle("Simplicity Native Multisig");
    await expect(creatorPage.getByRole("heading", { name: "Simplicity Native Multisig" }))
      .toBeVisible();

    await creatorPage.getByRole("button", { name: "Create", exact: true }).click();
    await creatorPage.getByRole("button", { name: "Demo keys", exact: true }).click();
    await expect(creatorPage.getByLabel("Participant key 1")).toHaveValue(/[0-9a-f]{64}/);
    await creatorPage.getByRole("button", { name: "Create multisig", exact: true }).click();

    const descriptorBlock = creatorPage
      .locator(".code-block")
      .filter({ hasText: "Shareable multisig descriptor" });
    await expect(descriptorBlock).toBeVisible();
    await expect(
      creatorPage.locator(".network-grid.tight").filter({ hasText: "Announcements" }),
    ).toContainText("0/3");

    const descriptorText = await descriptorBlock.locator("code").innerText();
    const descriptor = JSON.parse(descriptorText) as {
      multisigAddress: string;
      multisigScriptPubkey: string;
      participants: unknown[];
    };

    expect(descriptor.multisigAddress).toMatch(/^tex1/);
    expect(descriptor.multisigScriptPubkey).toMatch(/^[0-9a-f]+$/);
    expect(descriptor.participants).toHaveLength(3);
    expect(descriptorText).not.toContain("voteDescriptor");
    expect(descriptorText).not.toContain("slip77");
    expect(descriptorText).not.toContain("ct(");

    const loaderPage = await loaderContext.newPage();
    await loaderPage.goto("/");
    await expect(loaderPage).toHaveTitle("Simplicity Native Multisig");
    await expect(loaderPage.getByRole("heading", { name: "No descriptor loaded" }))
      .toBeVisible();
    await expect(loaderPage.getByText(descriptor.multisigAddress)).toHaveCount(0);

    await loaderPage.getByRole("button", { name: "Setup", exact: true }).click();
    await loaderPage
      .getByPlaceholder("Paste multisig descriptor JSON")
      .fill(descriptorText);
    await loaderPage.getByRole("button", { name: "Load", exact: true }).click();

    await expect(
      loaderPage.getByRole("heading", {
        name: /tex1pfzqs2mnzvmt96\.\.\.ugsw2qlq83kskdzf2t/,
      }),
    ).toBeVisible();

    await loaderPage.getByRole("button", { name: "Create", exact: true }).click();
    await expect(loaderPage.getByText("Shareable multisig descriptor")).toBeVisible();
    await expect(loaderPage.getByText("Recovered participants")).toBeVisible();
    await expect(loaderPage.getByText("Waiting for announcement")).toHaveCount(3);
    await expect(
      loaderPage.locator(".network-grid.tight").filter({ hasText: "Announcements" }),
    ).toContainText("0/3");
  } finally {
    await creatorContext.close();
    await loaderContext.close();
  }
});

test("obvious creation edge cases are surfaced without creating a descriptor", async ({
  page,
}) => {
  await page.goto("/");
  await page.getByRole("button", { name: "Create", exact: true }).click();
  await page.getByRole("button", { name: "Create multisig", exact: true }).click();

  await expect(page.locator(".toast.error")).toContainText("Creating multisig descriptor");
  await expect(page.getByText("Shareable multisig descriptor")).toHaveCount(0);

  await page.locator(".toast.error button").click();
  await page.getByRole("button", { name: "Demo keys", exact: true }).click();
  await expect(page.getByLabel("Participant key 1")).toHaveValue(/[0-9a-f]{64}/);
  const duplicateKey = await page.getByLabel("Participant key 1").inputValue();
  await page.getByLabel("Participant key 3").fill(duplicateKey);
  await page.getByRole("button", { name: "Create multisig", exact: true }).click();

  await expect(page.locator(".toast.error")).toContainText("participants must be distinct");
  await expect(page.getByText("Shareable multisig descriptor")).toHaveCount(0);
});

test("malformed descriptor load stays isolated and reports an error", async ({ page }) => {
  await page.goto("/");
  await page.getByRole("button", { name: "Setup", exact: true }).click();
  await page.getByPlaceholder("Paste multisig descriptor JSON").fill("{ not-json");
  await page.getByRole("button", { name: "Load", exact: true }).click();

  await expect(page.locator(".toast.error")).toContainText("Inspecting descriptor");
  await expect(page.getByRole("heading", { name: "No descriptor loaded" })).toBeVisible();
  await expect(page.getByText("Shareable multisig descriptor")).toHaveCount(0);
});

test("publish funding fee rate is relay-safe for vote and announcement broadcasts", () => {
  expect(publishFundingFeeRate).toBeGreaterThanOrEqual(1_000);
});

test("announcement dust amount must be a whole positive satoshi amount", async ({ page }) => {
  await page.goto("/");
  await page.getByRole("button", { name: "Create", exact: true }).click();
  await page.getByRole("button", { name: "Demo keys", exact: true }).click();
  await expect(page.getByLabel("Participant key 1")).toHaveValue(/[0-9a-f]{64}/);
  await page.getByRole("button", { name: "Create multisig", exact: true }).click();
  await expect(page.getByText("Shareable multisig descriptor")).toBeVisible();

  const publishButton = page.getByRole("button", { name: "Publish announcement" });
  await expect(publishButton).toBeEnabled();

  await page.getByLabel("Dust amount").fill("0");
  await expect(page.getByText("Dust amount must be a whole positive satoshi amount."))
    .toBeVisible();
  await expect(publishButton).toBeDisabled();

  await page.getByLabel("Dust amount").fill("-1");
  await expect(publishButton).toBeDisabled();

  await page.getByLabel("Dust amount").fill("1.5");
  await expect(publishButton).toBeDisabled();

  await page.getByLabel("Dust amount").fill("1000");
  await expect(page.getByText("Dust amount must be a whole positive satoshi amount."))
    .toHaveCount(0);
  await expect(publishButton).toBeEnabled();
});

test("publish helpers reject invalid stake amounts before LWK work", async () => {
  await expect(
    publishVote({} as never, {} as never, {} as never, {} as never, 0),
  ).rejects.toThrow("Vote amount must be a whole positive satoshi amount.");
  await expect(
    publishVote({} as never, {} as never, {} as never, {} as never, 1.5),
  ).rejects.toThrow("Vote amount must be a whole positive satoshi amount.");
  await expect(
    publishParticipantAnnouncement({} as never, {} as never, "", -1),
  ).rejects.toThrow("Dust amount must be a whole positive satoshi amount.");
});
