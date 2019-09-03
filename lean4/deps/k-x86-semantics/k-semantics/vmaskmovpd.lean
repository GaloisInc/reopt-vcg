def vmaskmovpd1 : instruction :=
  definst "vmaskmovpd" $ do
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 128)) (v_2505 : reg (bv 128)) => do
      v_9874 <- getRegister v_2504;
      v_9877 <- evaluateAddress v_2503;
      v_9878 <- load v_9877 16;
      setRegister (lhs.of_reg v_2505) (concat (mux (eq (extract v_9874 0 1) (expression.bv_nat 1 1)) (extract v_9878 0 64) (expression.bv_nat 64 0)) (mux (eq (extract v_9874 64 65) (expression.bv_nat 1 1)) (extract v_9878 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2508 : Mem) (v_2509 : reg (bv 256)) (v_2510 : reg (bv 256)) => do
      v_9887 <- getRegister v_2509;
      v_9890 <- evaluateAddress v_2508;
      v_9891 <- load v_9890 32;
      setRegister (lhs.of_reg v_2510) (concat (mux (eq (extract v_9887 0 1) (expression.bv_nat 1 1)) (extract v_9891 0 64) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_9887 64 65) (expression.bv_nat 1 1)) (extract v_9891 64 128) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_9887 128 129) (expression.bv_nat 1 1)) (extract v_9891 128 192) (expression.bv_nat 64 0)) (mux (eq (extract v_9887 192 193) (expression.bv_nat 1 1)) (extract v_9891 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) (v_2493 : Mem) => do
      v_12598 <- evaluateAddress v_2493;
      v_12599 <- getRegister v_2495;
      v_12602 <- getRegister v_2494;
      v_12604 <- load v_12598 16;
      store v_12598 (concat (mux (eq (extract v_12599 0 1) (expression.bv_nat 1 1)) (extract v_12602 0 64) (extract v_12604 0 64)) (mux (eq (extract v_12599 64 65) (expression.bv_nat 1 1)) (extract v_12602 64 128) (extract v_12604 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_2499 : reg (bv 256)) (v_2500 : reg (bv 256)) (v_2498 : Mem) => do
      v_12614 <- evaluateAddress v_2498;
      v_12615 <- getRegister v_2500;
      v_12618 <- getRegister v_2499;
      v_12620 <- load v_12614 32;
      store v_12614 (concat (mux (eq (extract v_12615 0 1) (expression.bv_nat 1 1)) (extract v_12618 0 64) (extract v_12620 0 64)) (concat (mux (eq (extract v_12615 64 65) (expression.bv_nat 1 1)) (extract v_12618 64 128) (extract v_12620 64 128)) (concat (mux (eq (extract v_12615 128 129) (expression.bv_nat 1 1)) (extract v_12618 128 192) (extract v_12620 128 192)) (mux (eq (extract v_12615 192 193) (expression.bv_nat 1 1)) (extract v_12618 192 256) (extract v_12620 192 256))))) 32;
      pure ()
    pat_end
