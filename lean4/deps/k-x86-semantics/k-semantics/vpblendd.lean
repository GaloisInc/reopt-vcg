def vpblendd1 : instruction :=
  definst "vpblendd" $ do
    pattern fun (v_2626 : imm int) (v_2621 : reg (bv 128)) (v_2622 : reg (bv 128)) (v_2623 : reg (bv 128)) => do
      v_6447 <- eval (handleImmediateWithSignExtend v_2626 8 8);
      v_6450 <- getRegister v_2622;
      v_6452 <- getRegister v_2621;
      setRegister (lhs.of_reg v_2623) (concat (mux (eq (extract v_6447 4 5) (expression.bv_nat 1 0)) (extract v_6450 0 32) (extract v_6452 0 32)) (concat (mux (eq (extract v_6447 5 6) (expression.bv_nat 1 0)) (extract v_6450 32 64) (extract v_6452 32 64)) (concat (mux (eq (extract v_6447 6 7) (expression.bv_nat 1 0)) (extract v_6450 64 96) (extract v_6452 64 96)) (mux (eq (extract v_6447 7 8) (expression.bv_nat 1 0)) (extract v_6450 96 128) (extract v_6452 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2636 : imm int) (v_2638 : reg (bv 256)) (v_2639 : reg (bv 256)) (v_2640 : reg (bv 256)) => do
      v_6480 <- eval (handleImmediateWithSignExtend v_2636 8 8);
      v_6483 <- getRegister v_2639;
      v_6485 <- getRegister v_2638;
      setRegister (lhs.of_reg v_2640) (concat (mux (eq (extract v_6480 0 1) (expression.bv_nat 1 0)) (extract v_6483 0 32) (extract v_6485 0 32)) (concat (mux (eq (extract v_6480 1 2) (expression.bv_nat 1 0)) (extract v_6483 32 64) (extract v_6485 32 64)) (concat (mux (eq (extract v_6480 2 3) (expression.bv_nat 1 0)) (extract v_6483 64 96) (extract v_6485 64 96)) (concat (mux (eq (extract v_6480 3 4) (expression.bv_nat 1 0)) (extract v_6483 96 128) (extract v_6485 96 128)) (concat (mux (eq (extract v_6480 4 5) (expression.bv_nat 1 0)) (extract v_6483 128 160) (extract v_6485 128 160)) (concat (mux (eq (extract v_6480 5 6) (expression.bv_nat 1 0)) (extract v_6483 160 192) (extract v_6485 160 192)) (concat (mux (eq (extract v_6480 6 7) (expression.bv_nat 1 0)) (extract v_6483 192 224) (extract v_6485 192 224)) (mux (eq (extract v_6480 7 8) (expression.bv_nat 1 0)) (extract v_6483 224 256) (extract v_6485 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2620 : imm int) (v_2619 : Mem) (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) => do
      v_15372 <- eval (handleImmediateWithSignExtend v_2620 8 8);
      v_15375 <- getRegister v_2615;
      v_15377 <- evaluateAddress v_2619;
      v_15378 <- load v_15377 16;
      setRegister (lhs.of_reg v_2616) (concat (mux (eq (extract v_15372 4 5) (expression.bv_nat 1 0)) (extract v_15375 0 32) (extract v_15378 0 32)) (concat (mux (eq (extract v_15372 5 6) (expression.bv_nat 1 0)) (extract v_15375 32 64) (extract v_15378 32 64)) (concat (mux (eq (extract v_15372 6 7) (expression.bv_nat 1 0)) (extract v_15375 64 96) (extract v_15378 64 96)) (mux (eq (extract v_15372 7 8) (expression.bv_nat 1 0)) (extract v_15375 96 128) (extract v_15378 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2631 : imm int) (v_2630 : Mem) (v_2632 : reg (bv 256)) (v_2633 : reg (bv 256)) => do
      v_15400 <- eval (handleImmediateWithSignExtend v_2631 8 8);
      v_15403 <- getRegister v_2632;
      v_15405 <- evaluateAddress v_2630;
      v_15406 <- load v_15405 32;
      setRegister (lhs.of_reg v_2633) (concat (mux (eq (extract v_15400 0 1) (expression.bv_nat 1 0)) (extract v_15403 0 32) (extract v_15406 0 32)) (concat (mux (eq (extract v_15400 1 2) (expression.bv_nat 1 0)) (extract v_15403 32 64) (extract v_15406 32 64)) (concat (mux (eq (extract v_15400 2 3) (expression.bv_nat 1 0)) (extract v_15403 64 96) (extract v_15406 64 96)) (concat (mux (eq (extract v_15400 3 4) (expression.bv_nat 1 0)) (extract v_15403 96 128) (extract v_15406 96 128)) (concat (mux (eq (extract v_15400 4 5) (expression.bv_nat 1 0)) (extract v_15403 128 160) (extract v_15406 128 160)) (concat (mux (eq (extract v_15400 5 6) (expression.bv_nat 1 0)) (extract v_15403 160 192) (extract v_15406 160 192)) (concat (mux (eq (extract v_15400 6 7) (expression.bv_nat 1 0)) (extract v_15403 192 224) (extract v_15406 192 224)) (mux (eq (extract v_15400 7 8) (expression.bv_nat 1 0)) (extract v_15403 224 256) (extract v_15406 224 256)))))))));
      pure ()
    pat_end
