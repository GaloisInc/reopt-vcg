def vmovdqu1 : instruction :=
  definst "vmovdqu" $ do
    pattern fun (v_2851 : Mem) (v_2852 : reg (bv 128)) => do
      v_10167 <- evaluateAddress v_2851;
      v_10168 <- load v_10167 16;
      setRegister (lhs.of_reg v_2852) v_10168;
      pure ()
    pat_end;
    pattern fun (v_2860 : Mem) (v_2861 : reg (bv 256)) => do
      v_10170 <- evaluateAddress v_2860;
      v_10171 <- load v_10170 32;
      setRegister (lhs.of_reg v_2861) v_10171;
      pure ()
    pat_end;
    pattern fun (v_2844 : reg (bv 128)) (v_2843 : Mem) => do
      v_12414 <- evaluateAddress v_2843;
      v_12415 <- getRegister v_2844;
      store v_12414 v_12415 16;
      pure ()
    pat_end;
    pattern fun (v_2848 : reg (bv 256)) (v_2847 : Mem) => do
      v_12417 <- evaluateAddress v_2847;
      v_12418 <- getRegister v_2848;
      store v_12417 v_12418 32;
      pure ()
    pat_end
