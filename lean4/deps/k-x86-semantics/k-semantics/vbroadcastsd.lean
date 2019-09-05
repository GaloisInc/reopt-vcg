def vbroadcastsd1 : instruction :=
  definst "vbroadcastsd" $ do
    pattern fun (v_2944 : reg (bv 128)) (v_2942 : reg (bv 256)) => do
      v_5460 <- getRegister v_2944;
      v_5461 <- eval (extract v_5460 64 128);
      setRegister (lhs.of_reg v_2942) (concat (concat (concat v_5461 v_5461) v_5461) v_5461);
      pure ()
    pat_end;
    pattern fun (v_2938 : Mem) (v_2939 : reg (bv 256)) => do
      v_9656 <- evaluateAddress v_2938;
      v_9657 <- load v_9656 8;
      setRegister (lhs.of_reg v_2939) (concat (concat (concat v_9657 v_9657) v_9657) v_9657);
      pure ()
    pat_end
