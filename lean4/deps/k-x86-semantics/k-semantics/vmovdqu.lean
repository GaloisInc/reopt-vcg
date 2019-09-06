def vmovdqu1 : instruction :=
  definst "vmovdqu" $ do
    pattern fun (v_2876 : Mem) (v_2877 : reg (bv 128)) => do
      v_10194 <- evaluateAddress v_2876;
      v_10195 <- load v_10194 16;
      setRegister (lhs.of_reg v_2877) v_10195;
      pure ()
    pat_end;
    pattern fun (v_2885 : Mem) (v_2886 : reg (bv 256)) => do
      v_10197 <- evaluateAddress v_2885;
      v_10198 <- load v_10197 32;
      setRegister (lhs.of_reg v_2886) v_10198;
      pure ()
    pat_end;
    pattern fun (v_2869 : reg (bv 128)) (v_2868 : Mem) => do
      v_12441 <- evaluateAddress v_2868;
      v_12442 <- getRegister v_2869;
      store v_12441 v_12442 16;
      pure ()
    pat_end;
    pattern fun (v_2873 : reg (bv 256)) (v_2872 : Mem) => do
      v_12444 <- evaluateAddress v_2872;
      v_12445 <- getRegister v_2873;
      store v_12444 v_12445 32;
      pure ()
    pat_end
