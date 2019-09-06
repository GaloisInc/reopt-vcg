def cmovbe1 : instruction :=
  definst "cmovbe" $ do
    pattern fun (v_2514 : Mem) (v_2517 : reg (bv 32)) => do
      v_8651 <- getRegister cf;
      v_8652 <- getRegister zf;
      v_8654 <- evaluateAddress v_2514;
      v_8655 <- load v_8654 4;
      v_8656 <- getRegister v_2517;
      setRegister (lhs.of_reg v_2517) (mux (bit_or v_8651 v_8652) v_8655 v_8656);
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2531 : reg (bv 64)) => do
      v_8659 <- getRegister cf;
      v_8660 <- getRegister zf;
      v_8662 <- evaluateAddress v_2532;
      v_8663 <- load v_8662 8;
      v_8664 <- getRegister v_2531;
      setRegister (lhs.of_reg v_2531) (mux (bit_or v_8659 v_8660) v_8663 v_8664);
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) (v_2549 : reg (bv 16)) => do
      v_8667 <- getRegister cf;
      v_8668 <- getRegister zf;
      v_8670 <- evaluateAddress v_2548;
      v_8671 <- load v_8670 2;
      v_8672 <- getRegister v_2549;
      setRegister (lhs.of_reg v_2549) (mux (bit_or v_8667 v_8668) v_8671 v_8672);
      pure ()
    pat_end
