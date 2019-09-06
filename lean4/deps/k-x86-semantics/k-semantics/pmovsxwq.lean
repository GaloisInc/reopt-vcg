def pmovsxwq1 : instruction :=
  definst "pmovsxwq" $ do
    pattern fun (v_2802 : reg (bv 128)) (v_2803 : reg (bv 128)) => do
      v_5544 <- getRegister v_2802;
      setRegister (lhs.of_reg v_2803) (concat (sext (extract v_5544 96 112) 64) (sext (extract v_5544 112 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2798 : Mem) (v_2799 : reg (bv 128)) => do
      v_12278 <- evaluateAddress v_2798;
      v_12279 <- load v_12278 4;
      setRegister (lhs.of_reg v_2799) (concat (sext (extract v_12279 0 16) 64) (sext (extract v_12279 16 32) 64));
      pure ()
    pat_end
