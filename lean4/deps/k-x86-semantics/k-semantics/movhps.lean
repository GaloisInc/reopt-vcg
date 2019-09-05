def movhps1 : instruction :=
  definst "movhps" $ do
    pattern fun (v_2526 : reg (bv 128)) (v_2525 : Mem) => do
      v_8436 <- evaluateAddress v_2525;
      v_8437 <- getRegister v_2526;
      store v_8436 (extract v_8437 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2529 : Mem) (v_2530 : reg (bv 128)) => do
      v_8698 <- evaluateAddress v_2529;
      v_8699 <- load v_8698 8;
      v_8700 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2530) (concat v_8699 (extract v_8700 64 128));
      pure ()
    pat_end
