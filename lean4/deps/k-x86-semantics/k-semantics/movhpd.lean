def movhpd1 : instruction :=
  definst "movhpd" $ do
    pattern fun (v_2544 : reg (bv 128)) (v_2543 : Mem) => do
      v_8458 <- evaluateAddress v_2543;
      v_8459 <- getRegister v_2544;
      store v_8458 (extract v_8459 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2547 : Mem) (v_2548 : reg (bv 128)) => do
      v_8719 <- evaluateAddress v_2547;
      v_8720 <- load v_8719 8;
      v_8721 <- getRegister v_2548;
      setRegister (lhs.of_reg v_2548) (concat v_8720 (extract v_8721 64 128));
      pure ()
    pat_end
