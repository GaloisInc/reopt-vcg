def movbew1 : instruction :=
  definst "movbew" $ do
    pattern fun (v_2385 : reg (bv 16)) (v_2384 : Mem) => do
      v_8560 <- evaluateAddress v_2384;
      v_8561 <- getRegister v_2385;
      store v_8560 (concat (extract v_8561 8 16) (extract v_8561 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2392 : Mem) (v_2393 : reg (bv 16)) => do
      v_8829 <- evaluateAddress v_2392;
      v_8830 <- load v_8829 2;
      setRegister (lhs.of_reg v_2393) (concat (extract v_8830 8 16) (extract v_8830 0 8));
      pure ()
    pat_end
