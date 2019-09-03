def vpbroadcastw1 : instruction :=
  definst "vpbroadcastw" $ do
    pattern fun (v_2741 : reg (bv 128)) (v_2742 : reg (bv 128)) => do
      v_7222 <- getRegister v_2741;
      v_7223 <- eval (extract v_7222 112 128);
      setRegister (lhs.of_reg v_2742) (concat v_7223 (concat v_7223 (concat v_7223 (concat v_7223 (concat v_7223 (concat v_7223 (concat v_7223 v_7223)))))));
      pure ()
    pat_end;
    pattern fun (v_2750 : reg (bv 128)) (v_2751 : reg (bv 256)) => do
      v_7236 <- getRegister v_2750;
      v_7237 <- eval (extract v_7236 112 128);
      setRegister (lhs.of_reg v_2751) (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 (concat v_7237 v_7237)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2736 : Mem) (v_2737 : reg (bv 128)) => do
      v_16467 <- evaluateAddress v_2736;
      v_16468 <- load v_16467 2;
      setRegister (lhs.of_reg v_2737) (concat v_16468 (concat v_16468 (concat v_16468 (concat v_16468 (concat v_16468 (concat v_16468 (concat v_16468 v_16468)))))));
      pure ()
    pat_end;
    pattern fun (v_2745 : Mem) (v_2746 : reg (bv 256)) => do
      v_16477 <- evaluateAddress v_2745;
      v_16478 <- load v_16477 2;
      setRegister (lhs.of_reg v_2746) (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 (concat v_16478 v_16478)))))))))))))));
      pure ()
    pat_end
