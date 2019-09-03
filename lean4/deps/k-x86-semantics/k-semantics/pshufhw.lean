def pshufhw1 : instruction :=
  definst "pshufhw" $ do
    pattern fun (v_2925 : imm int) (v_2926 : reg (bv 128)) (v_2927 : reg (bv 128)) => do
      v_7181 <- getRegister v_2926;
      v_7182 <- eval (handleImmediateWithSignExtend v_2925 8 8);
      setRegister (lhs.of_reg v_2927) (concat (extract (lshr v_7181 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7182 0 2)) 4) 0 128))) 48 64) (concat (extract (lshr v_7181 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7182 2 4)) 4) 0 128))) 48 64) (concat (extract (lshr v_7181 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7182 4 6)) 4) 0 128))) 48 64) (concat (extract (lshr v_7181 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7182 6 8)) 4) 0 128))) 48 64) (extract v_7181 64 128)))));
      pure ()
    pat_end;
    pattern fun (v_2921 : imm int) (v_2920 : Mem) (v_2922 : reg (bv 128)) => do
      v_14074 <- evaluateAddress v_2920;
      v_14075 <- load v_14074 16;
      v_14076 <- eval (handleImmediateWithSignExtend v_2921 8 8);
      setRegister (lhs.of_reg v_2922) (concat (extract (lshr v_14075 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14076 0 2)) 4) 0 128))) 48 64) (concat (extract (lshr v_14075 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14076 2 4)) 4) 0 128))) 48 64) (concat (extract (lshr v_14075 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14076 4 6)) 4) 0 128))) 48 64) (concat (extract (lshr v_14075 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14076 6 8)) 4) 0 128))) 48 64) (extract v_14075 64 128)))));
      pure ()
    pat_end
