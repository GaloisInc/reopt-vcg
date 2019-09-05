def movhpd1 : instruction :=
  definst "movhpd" $ do
    pattern fun (v_2518 : reg (bv 128)) (v_2517 : Mem) => do
      v_8431 <- evaluateAddress v_2517;
      v_8432 <- getRegister v_2518;
      store v_8431 (extract v_8432 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2522 : reg (bv 128)) => do
      v_8692 <- evaluateAddress v_2521;
      v_8693 <- load v_8692 8;
      v_8694 <- getRegister v_2522;
      setRegister (lhs.of_reg v_2522) (concat v_8693 (extract v_8694 64 128));
      pure ()
    pat_end
