def punpcklwd1 : instruction :=
  definst "punpcklwd" $ do
    pattern fun (v_3225 : reg (bv 128)) (v_3226 : reg (bv 128)) => do
      v_9191 <- getRegister v_3225;
      v_9193 <- getRegister v_3226;
      setRegister (lhs.of_reg v_3226) (concat (concat (extract v_9191 64 80) (extract v_9193 64 80)) (concat (concat (extract v_9191 80 96) (extract v_9193 80 96)) (concat (concat (extract v_9191 96 112) (extract v_9193 96 112)) (concat (extract v_9191 112 128) (extract v_9193 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_3220 : Mem) (v_3221 : reg (bv 128)) => do
      v_16060 <- evaluateAddress v_3220;
      v_16061 <- load v_16060 16;
      v_16063 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3221) (concat (concat (extract v_16061 64 80) (extract v_16063 64 80)) (concat (concat (extract v_16061 80 96) (extract v_16063 80 96)) (concat (concat (extract v_16061 96 112) (extract v_16063 96 112)) (concat (extract v_16061 112 128) (extract v_16063 112 128)))));
      pure ()
    pat_end
