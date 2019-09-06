def movbew1 : instruction :=
  definst "movbew" $ do
    pattern fun (v_2474 : reg (bv 16)) (v_2473 : Mem) => do
      v_8431 <- evaluateAddress v_2473;
      v_8432 <- getRegister v_2474;
      store v_8431 (concat (extract v_8432 8 16) (extract v_8432 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2481 : Mem) (v_2482 : reg (bv 16)) => do
      v_8699 <- evaluateAddress v_2481;
      v_8700 <- load v_8699 2;
      setRegister (lhs.of_reg v_2482) (concat (extract v_8700 8 16) (extract v_8700 0 8));
      pure ()
    pat_end
