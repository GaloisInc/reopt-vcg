def vpsllq1 : instruction :=
  definst "vpsllq" $ do
    pattern fun (v_3091 : imm int) (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) => do
      v_7762 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3091 8 8));
      v_7764 <- getRegister v_3093;
      v_7766 <- eval (uvalueMInt v_7762);
      setRegister (lhs.of_reg v_3094) (mux (ugt v_7762 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7764 0 64) v_7766) 0 64) (extract (shl (extract v_7764 64 128) v_7766) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3103 : reg (bv 128)) (v_3104 : reg (bv 128)) (v_3105 : reg (bv 128)) => do
      v_7780 <- getRegister v_3103;
      v_7781 <- eval (extract v_7780 64 128);
      v_7783 <- getRegister v_3104;
      v_7785 <- eval (uvalueMInt v_7781);
      setRegister (lhs.of_reg v_3105) (mux (ugt v_7781 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7783 0 64) v_7785) 0 64) (extract (shl (extract v_7783 64 128) v_7785) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3108 : imm int) (v_3111 : reg (bv 256)) (v_3112 : reg (bv 256)) => do
      v_7795 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3108 8 8));
      v_7797 <- getRegister v_3111;
      v_7799 <- eval (uvalueMInt v_7795);
      setRegister (lhs.of_reg v_3112) (mux (ugt v_7795 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7797 0 64) v_7799) 0 64) (concat (extract (shl (extract v_7797 64 128) v_7799) 0 64) (concat (extract (shl (extract v_7797 128 192) v_7799) 0 64) (extract (shl (extract v_7797 192 256) v_7799) 0 64)))));
      pure ()
    pat_end;
    pattern fun (v_3120 : reg (bv 128)) (v_3122 : reg (bv 256)) (v_3123 : reg (bv 256)) => do
      v_7821 <- getRegister v_3120;
      v_7822 <- eval (extract v_7821 64 128);
      v_7824 <- getRegister v_3122;
      v_7826 <- eval (uvalueMInt v_7822);
      setRegister (lhs.of_reg v_3123) (mux (ugt v_7822 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7824 0 64) v_7826) 0 64) (concat (extract (shl (extract v_7824 64 128) v_7826) 0 64) (concat (extract (shl (extract v_7824 128 192) v_7826) 0 64) (extract (shl (extract v_7824 192 256) v_7826) 0 64)))));
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3098 : reg (bv 128)) (v_3099 : reg (bv 128)) => do
      v_14197 <- evaluateAddress v_3097;
      v_14198 <- load v_14197 16;
      v_14199 <- eval (extract v_14198 64 128);
      v_14201 <- getRegister v_3098;
      v_14203 <- eval (uvalueMInt v_14199);
      setRegister (lhs.of_reg v_3099) (mux (ugt v_14199 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14201 0 64) v_14203) 0 64) (extract (shl (extract v_14201 64 128) v_14203) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3114 : Mem) (v_3116 : reg (bv 256)) (v_3117 : reg (bv 256)) => do
      v_14212 <- evaluateAddress v_3114;
      v_14213 <- load v_14212 16;
      v_14214 <- eval (extract v_14213 64 128);
      v_14216 <- getRegister v_3116;
      v_14218 <- eval (uvalueMInt v_14214);
      setRegister (lhs.of_reg v_3117) (mux (ugt v_14214 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14216 0 64) v_14218) 0 64) (concat (extract (shl (extract v_14216 64 128) v_14218) 0 64) (concat (extract (shl (extract v_14216 128 192) v_14218) 0 64) (extract (shl (extract v_14216 192 256) v_14218) 0 64)))));
      pure ()
    pat_end
