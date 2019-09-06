def movbe1 : instruction :=
  definst "movbe" $ do
    pattern fun (v_2470 : reg (bv 16)) (v_2469 : Mem) => do
      v_8692 <- evaluateAddress v_2469;
      v_8693 <- getRegister v_2470;
      store v_8692 (concat (extract v_8693 8 16) (extract v_8693 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 16)) => do
      v_10695 <- evaluateAddress v_2477;
      v_10696 <- load v_10695 2;
      setRegister (lhs.of_reg v_2478) (concat (extract v_10696 8 16) (extract v_10696 0 8));
      pure ()
    pat_end
