def vbroadcastss1 : instruction :=
  definst "vbroadcastss" $ do
    pattern fun (v_2901 : reg (bv 128)) (v_2902 : reg (bv 128)) => do
      v_6001 <- getRegister v_2901;
      v_6002 <- eval (extract v_6001 96 128);
      setRegister (lhs.of_reg v_2902) (concat (concat (concat v_6002 v_6002) v_6002) v_6002);
      pure ()
    pat_end;
    pattern fun (v_2911 : reg (bv 128)) (v_2907 : reg (bv 256)) => do
      v_6011 <- getRegister v_2911;
      v_6012 <- eval (extract v_6011 96 128);
      setRegister (lhs.of_reg v_2907) (concat (concat (concat (concat (concat (concat (concat v_6012 v_6012) v_6012) v_6012) v_6012) v_6012) v_6012) v_6012);
      pure ()
    pat_end;
    pattern fun (v_2894 : Mem) (v_2897 : reg (bv 128)) => do
      v_11436 <- evaluateAddress v_2894;
      v_11437 <- load v_11436 4;
      setRegister (lhs.of_reg v_2897) (concat (concat (concat v_11437 v_11437) v_11437) v_11437);
      pure ()
    pat_end;
    pattern fun (v_2903 : Mem) (v_2904 : reg (bv 256)) => do
      v_11442 <- evaluateAddress v_2903;
      v_11443 <- load v_11442 4;
      setRegister (lhs.of_reg v_2904) (concat (concat (concat (concat (concat (concat (concat v_11443 v_11443) v_11443) v_11443) v_11443) v_11443) v_11443) v_11443);
      pure ()
    pat_end
