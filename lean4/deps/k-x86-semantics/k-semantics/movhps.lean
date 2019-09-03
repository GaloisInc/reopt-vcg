def movhps1 : instruction :=
  definst "movhps" $ do
    pattern fun (v_2463 : reg (bv 128)) (v_2462 : Mem) => do
      v_8592 <- evaluateAddress v_2462;
      v_8593 <- getRegister v_2463;
      store v_8592 (extract v_8593 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2466 : Mem) (v_2467 : reg (bv 128)) => do
      v_8855 <- evaluateAddress v_2466;
      v_8856 <- load v_8855 8;
      v_8857 <- getRegister v_2467;
      setRegister (lhs.of_reg v_2467) (concat v_8856 (extract v_8857 64 128));
      pure ()
    pat_end
