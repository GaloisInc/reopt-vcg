def vmaskmovpd1 : instruction :=
  definst "vmaskmovpd" $ do
    pattern fun (v_2567 : Mem) (v_2568 : reg (bv 128)) (v_2569 : reg (bv 128)) => do
      v_9758 <- getRegister v_2568;
      v_9760 <- evaluateAddress v_2567;
      v_9761 <- load v_9760 16;
      setRegister (lhs.of_reg v_2569) (concat (mux (isBitSet v_9758 0) (extract v_9761 0 64) (expression.bv_nat 64 0)) (mux (isBitSet v_9758 64) (extract v_9761 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2572 : Mem) (v_2573 : reg (bv 256)) (v_2574 : reg (bv 256)) => do
      v_9769 <- getRegister v_2573;
      v_9771 <- evaluateAddress v_2572;
      v_9772 <- load v_9771 32;
      setRegister (lhs.of_reg v_2574) (concat (mux (isBitSet v_9769 0) (extract v_9772 0 64) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_9769 64) (extract v_9772 64 128) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_9769 128) (extract v_9772 128 192) (expression.bv_nat 64 0)) (mux (isBitSet v_9769 192) (extract v_9772 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2558 : reg (bv 128)) (v_2559 : reg (bv 128)) (v_2557 : Mem) => do
      v_12296 <- evaluateAddress v_2557;
      v_12297 <- getRegister v_2559;
      v_12299 <- getRegister v_2558;
      v_12301 <- load v_12296 16;
      store v_12296 (concat (mux (isBitSet v_12297 0) (extract v_12299 0 64) (extract v_12301 0 64)) (mux (isBitSet v_12297 64) (extract v_12299 64 128) (extract v_12301 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_2563 : reg (bv 256)) (v_2564 : reg (bv 256)) (v_2562 : Mem) => do
      v_12310 <- evaluateAddress v_2562;
      v_12311 <- getRegister v_2564;
      v_12313 <- getRegister v_2563;
      v_12315 <- load v_12310 32;
      store v_12310 (concat (mux (isBitSet v_12311 0) (extract v_12313 0 64) (extract v_12315 0 64)) (concat (mux (isBitSet v_12311 64) (extract v_12313 64 128) (extract v_12315 64 128)) (concat (mux (isBitSet v_12311 128) (extract v_12313 128 192) (extract v_12315 128 192)) (mux (isBitSet v_12311 192) (extract v_12313 192 256) (extract v_12315 192 256))))) 32;
      pure ()
    pat_end
