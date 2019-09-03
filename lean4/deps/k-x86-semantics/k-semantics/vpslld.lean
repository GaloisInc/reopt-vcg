def vpslld1 : instruction :=
  definst "vpslld" $ do
    pattern fun (v_3045 : imm int) (v_3047 : reg (bv 128)) (v_3048 : reg (bv 128)) => do
      v_7598 <- eval (handleImmediateWithSignExtend v_3045 8 8);
      v_7601 <- getRegister v_3047;
      v_7604 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7598));
      setRegister (lhs.of_reg v_3048) (mux (ugt (concat (expression.bv_nat 56 0) v_7598) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7601 0 32) v_7604) 0 32) (concat (extract (shl (extract v_7601 32 64) v_7604) 0 32) (concat (extract (shl (extract v_7601 64 96) v_7604) 0 32) (extract (shl (extract v_7601 96 128) v_7604) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3057 : reg (bv 128)) (v_3058 : reg (bv 128)) (v_3059 : reg (bv 128)) => do
      v_7626 <- getRegister v_3057;
      v_7629 <- getRegister v_3058;
      v_7632 <- eval (uvalueMInt (extract v_7626 96 128));
      setRegister (lhs.of_reg v_3059) (mux (ugt (extract v_7626 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7629 0 32) v_7632) 0 32) (concat (extract (shl (extract v_7629 32 64) v_7632) 0 32) (concat (extract (shl (extract v_7629 64 96) v_7632) 0 32) (extract (shl (extract v_7629 96 128) v_7632) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3062 : imm int) (v_3065 : reg (bv 256)) (v_3066 : reg (bv 256)) => do
      v_7649 <- eval (handleImmediateWithSignExtend v_3062 8 8);
      v_7652 <- getRegister v_3065;
      v_7655 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7649));
      setRegister (lhs.of_reg v_3066) (mux (ugt (concat (expression.bv_nat 56 0) v_7649) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7652 0 32) v_7655) 0 32) (concat (extract (shl (extract v_7652 32 64) v_7655) 0 32) (concat (extract (shl (extract v_7652 64 96) v_7655) 0 32) (concat (extract (shl (extract v_7652 96 128) v_7655) 0 32) (concat (extract (shl (extract v_7652 128 160) v_7655) 0 32) (concat (extract (shl (extract v_7652 160 192) v_7655) 0 32) (concat (extract (shl (extract v_7652 192 224) v_7655) 0 32) (extract (shl (extract v_7652 224 256) v_7655) 0 32)))))))));
      pure ()
    pat_end;
    pattern fun (v_3074 : reg (bv 128)) (v_3076 : reg (bv 256)) (v_3077 : reg (bv 256)) => do
      v_7693 <- getRegister v_3074;
      v_7696 <- getRegister v_3076;
      v_7699 <- eval (uvalueMInt (extract v_7693 96 128));
      setRegister (lhs.of_reg v_3077) (mux (ugt (extract v_7693 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7696 0 32) v_7699) 0 32) (concat (extract (shl (extract v_7696 32 64) v_7699) 0 32) (concat (extract (shl (extract v_7696 64 96) v_7699) 0 32) (concat (extract (shl (extract v_7696 96 128) v_7699) 0 32) (concat (extract (shl (extract v_7696 128 160) v_7699) 0 32) (concat (extract (shl (extract v_7696 160 192) v_7699) 0 32) (concat (extract (shl (extract v_7696 192 224) v_7699) 0 32) (extract (shl (extract v_7696 224 256) v_7699) 0 32)))))))));
      pure ()
    pat_end;
    pattern fun (v_3051 : Mem) (v_3052 : reg (bv 128)) (v_3053 : reg (bv 128)) => do
      v_14133 <- evaluateAddress v_3051;
      v_14134 <- load v_14133 16;
      v_14137 <- getRegister v_3052;
      v_14140 <- eval (uvalueMInt (extract v_14134 96 128));
      setRegister (lhs.of_reg v_3053) (mux (ugt (extract v_14134 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14137 0 32) v_14140) 0 32) (concat (extract (shl (extract v_14137 32 64) v_14140) 0 32) (concat (extract (shl (extract v_14137 64 96) v_14140) 0 32) (extract (shl (extract v_14137 96 128) v_14140) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3068 : Mem) (v_3070 : reg (bv 256)) (v_3071 : reg (bv 256)) => do
      v_14157 <- evaluateAddress v_3068;
      v_14158 <- load v_14157 16;
      v_14161 <- getRegister v_3070;
      v_14164 <- eval (uvalueMInt (extract v_14158 96 128));
      setRegister (lhs.of_reg v_3071) (mux (ugt (extract v_14158 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14161 0 32) v_14164) 0 32) (concat (extract (shl (extract v_14161 32 64) v_14164) 0 32) (concat (extract (shl (extract v_14161 64 96) v_14164) 0 32) (concat (extract (shl (extract v_14161 96 128) v_14164) 0 32) (concat (extract (shl (extract v_14161 128 160) v_14164) 0 32) (concat (extract (shl (extract v_14161 160 192) v_14164) 0 32) (concat (extract (shl (extract v_14161 192 224) v_14164) 0 32) (extract (shl (extract v_14161 224 256) v_14164) 0 32)))))))));
      pure ()
    pat_end
