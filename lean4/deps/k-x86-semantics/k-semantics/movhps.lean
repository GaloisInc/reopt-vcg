def movhps1 : instruction :=
  definst "movhps" $ do
    pattern fun (v_2476 : reg (bv 128)) (v_2475 : Mem) => do
      v_8572 <- evaluateAddress v_2475;
      v_8573 <- getRegister v_2476;
      store v_8572 (extract v_8573 0 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2479 : Mem) (v_2480 : reg (bv 128)) => do
      v_8834 <- evaluateAddress v_2479;
      v_8835 <- load v_8834 8;
      v_8836 <- getRegister v_2480;
      setRegister (lhs.of_reg v_2480) (concat v_8835 (extract v_8836 64 128));
      pure ()
    pat_end
