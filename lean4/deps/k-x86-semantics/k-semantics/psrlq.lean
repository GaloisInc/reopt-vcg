def psrlq1 : instruction :=
  definst "psrlq" $ do
    pattern fun (v_3063 : imm int) (v_3064 : reg (bv 128)) => do
      v_7914 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3063 8 8));
      v_7916 <- getRegister v_3064;
      v_7918 <- eval (uvalueMInt v_7914);
      setRegister (lhs.of_reg v_3064) (mux (ugt v_7914 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_7916 0 64) v_7918) (lshr (extract v_7916 64 128) v_7918)));
      pure ()
    pat_end;
    pattern fun (v_3072 : reg (bv 128)) (v_3073 : reg (bv 128)) => do
      v_7929 <- getRegister v_3072;
      v_7930 <- eval (extract v_7929 64 128);
      v_7932 <- getRegister v_3073;
      v_7934 <- eval (uvalueMInt v_7930);
      setRegister (lhs.of_reg v_3073) (mux (ugt v_7930 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_7932 0 64) v_7934) (lshr (extract v_7932 64 128) v_7934)));
      pure ()
    pat_end;
    pattern fun (v_3068 : Mem) (v_3069 : reg (bv 128)) => do
      v_14584 <- evaluateAddress v_3068;
      v_14585 <- load v_14584 16;
      v_14586 <- eval (extract v_14585 64 128);
      v_14588 <- getRegister v_3069;
      v_14590 <- eval (uvalueMInt v_14586);
      setRegister (lhs.of_reg v_3069) (mux (ugt v_14586 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_14588 0 64) v_14590) (lshr (extract v_14588 64 128) v_14590)));
      pure ()
    pat_end
