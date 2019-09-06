def vmovhpd1 : instruction :=
  definst "vmovhpd" $ do
    pattern fun (v_2904 : Mem) (v_2905 : reg (bv 128)) (v_2906 : reg (bv 128)) => do
      v_10201 <- evaluateAddress v_2904;
      v_10202 <- load v_10201 8;
      v_10203 <- getRegister v_2905;
      setRegister (lhs.of_reg v_2906) (concat v_10202 (extract v_10203 64 128));
      pure ()
    pat_end;
    pattern fun (v_2901 : reg (bv 128)) (v_2900 : Mem) => do
      v_12447 <- evaluateAddress v_2900;
      v_12448 <- getRegister v_2901;
      store v_12447 (extract v_12448 0 64) 8;
      pure ()
    pat_end
