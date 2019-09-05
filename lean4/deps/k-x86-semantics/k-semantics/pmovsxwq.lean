def pmovsxwq1 : instruction :=
  definst "pmovsxwq" $ do
    pattern fun (v_2774 : reg (bv 128)) (v_2775 : reg (bv 128)) => do
      v_5517 <- getRegister v_2774;
      setRegister (lhs.of_reg v_2775) (concat (sext (extract v_5517 96 112) 64) (sext (extract v_5517 112 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2771 : Mem) (v_2770 : reg (bv 128)) => do
      v_12302 <- evaluateAddress v_2771;
      v_12303 <- load v_12302 4;
      setRegister (lhs.of_reg v_2770) (concat (sext (extract v_12303 0 16) 64) (sext (extract v_12303 16 32) 64));
      pure ()
    pat_end
