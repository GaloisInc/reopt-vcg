def shufpd1 : instruction :=
  definst "shufpd" $ do
    pattern fun (v_3035 : imm int) (v_3037 : reg (bv 128)) (v_3038 : reg (bv 128)) => do
      v_6661 <- eval (handleImmediateWithSignExtend v_3035 8 8);
      v_6664 <- getRegister v_3037;
      v_6670 <- getRegister v_3038;
      setRegister (lhs.of_reg v_3038) (concat (mux (eq (extract v_6661 6 7) (expression.bv_nat 1 1)) (extract v_6664 0 64) (extract v_6664 64 128)) (mux (eq (extract v_6661 7 8) (expression.bv_nat 1 1)) (extract v_6670 0 64) (extract v_6670 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3030 : imm int) (v_3031 : Mem) (v_3032 : reg (bv 128)) => do
      v_10189 <- eval (handleImmediateWithSignExtend v_3030 8 8);
      v_10192 <- evaluateAddress v_3031;
      v_10193 <- load v_10192 16;
      v_10199 <- getRegister v_3032;
      setRegister (lhs.of_reg v_3032) (concat (mux (eq (extract v_10189 6 7) (expression.bv_nat 1 1)) (extract v_10193 0 64) (extract v_10193 64 128)) (mux (eq (extract v_10189 7 8) (expression.bv_nat 1 1)) (extract v_10199 0 64) (extract v_10199 64 128)));
      pure ()
    pat_end
