def vpslldq1 : instruction :=
  definst "vpslldq" $ do
    pattern fun (v_3070 : imm int) (v_3068 : reg (bv 128)) (v_3069 : reg (bv 128)) => do
      v_8045 <- getRegister v_3068;
      v_8046 <- eval (handleImmediateWithSignExtend v_3070 8 8);
      v_8049 <- eval (mux (ugt v_8046 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8046));
      setRegister (lhs.of_reg v_3069) (extract (shl v_8045 (uvalueMInt (extract (shl v_8049 3) 0 (bitwidthMInt v_8049)))) 0 (bitwidthMInt v_8045));
      pure ()
    pat_end;
    pattern fun (v_3074 : imm int) (v_3075 : reg (bv 256)) (v_3076 : reg (bv 256)) => do
      v_8058 <- getRegister v_3075;
      v_8059 <- eval (extract v_8058 0 128);
      v_8060 <- eval (handleImmediateWithSignExtend v_3074 8 8);
      v_8063 <- eval (mux (ugt v_8060 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8060));
      v_8067 <- eval (uvalueMInt (extract (shl v_8063 3) 0 (bitwidthMInt v_8063)));
      v_8071 <- eval (extract v_8058 128 256);
      setRegister (lhs.of_reg v_3076) (concat (extract (shl v_8059 v_8067) 0 (bitwidthMInt v_8059)) (extract (shl v_8071 v_8067) 0 (bitwidthMInt v_8071)));
      pure ()
    pat_end
