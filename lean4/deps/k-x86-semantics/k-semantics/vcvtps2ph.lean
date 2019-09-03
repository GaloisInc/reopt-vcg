def vcvtps2ph1 : instruction :=
  definst "vcvtps2ph" $ do
    pattern fun (v_3140 : imm int) (v_3144 : reg (bv 128)) (v_3145 : reg (bv 128)) => do
      v_6731 <- getRegister v_3144;
      v_6732 <- eval (extract v_6731 0 32);
      v_6741 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3140 8 8));
      v_6744 <- eval (extract v_6731 32 64);
      v_6754 <- eval (extract v_6731 64 96);
      v_6764 <- eval (extract v_6731 96 128);
      setRegister (lhs.of_reg v_3145) (concat (expression.bv_nat 64 0) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6732 0 1)) (uvalueMInt (extract v_6732 1 9)) (uvalueMInt (extract v_6732 9 32))) v_6741) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6744 0 1)) (uvalueMInt (extract v_6744 1 9)) (uvalueMInt (extract v_6744 9 32))) v_6741) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6754 0 1)) (uvalueMInt (extract v_6754 1 9)) (uvalueMInt (extract v_6754 9 32))) v_6741) 16) (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6764 0 1)) (uvalueMInt (extract v_6764 1 9)) (uvalueMInt (extract v_6764 9 32))) v_6741) 16)))));
      pure ()
    pat_end;
    pattern fun (v_3146 : imm int) (v_3147 : reg (bv 256)) (v_3151 : reg (bv 128)) => do
      v_6779 <- getRegister v_3147;
      v_6780 <- eval (extract v_6779 0 32);
      v_6789 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3146 8 8));
      v_6792 <- eval (extract v_6779 32 64);
      v_6802 <- eval (extract v_6779 64 96);
      v_6812 <- eval (extract v_6779 96 128);
      v_6822 <- eval (extract v_6779 128 160);
      v_6832 <- eval (extract v_6779 160 192);
      v_6842 <- eval (extract v_6779 192 224);
      v_6852 <- eval (extract v_6779 224 256);
      setRegister (lhs.of_reg v_3151) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6780 0 1)) (uvalueMInt (extract v_6780 1 9)) (uvalueMInt (extract v_6780 9 32))) v_6789) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6792 0 1)) (uvalueMInt (extract v_6792 1 9)) (uvalueMInt (extract v_6792 9 32))) v_6789) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6802 0 1)) (uvalueMInt (extract v_6802 1 9)) (uvalueMInt (extract v_6802 9 32))) v_6789) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6812 0 1)) (uvalueMInt (extract v_6812 1 9)) (uvalueMInt (extract v_6812 9 32))) v_6789) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6822 0 1)) (uvalueMInt (extract v_6822 1 9)) (uvalueMInt (extract v_6822 9 32))) v_6789) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6832 0 1)) (uvalueMInt (extract v_6832 1 9)) (uvalueMInt (extract v_6832 9 32))) v_6789) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6842 0 1)) (uvalueMInt (extract v_6842 1 9)) (uvalueMInt (extract v_6842 9 32))) v_6789) 16) (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6852 0 1)) (uvalueMInt (extract v_6852 1 9)) (uvalueMInt (extract v_6852 9 32))) v_6789) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_3131 : imm int) (v_3132 : reg (bv 256)) (v_3130 : Mem) => do
      v_13119 <- evaluateAddress v_3130;
      v_13120 <- getRegister v_3132;
      v_13121 <- eval (extract v_13120 0 32);
      v_13130 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3131 8 8));
      v_13133 <- eval (extract v_13120 32 64);
      v_13143 <- eval (extract v_13120 64 96);
      v_13153 <- eval (extract v_13120 96 128);
      v_13163 <- eval (extract v_13120 128 160);
      v_13173 <- eval (extract v_13120 160 192);
      v_13183 <- eval (extract v_13120 192 224);
      v_13193 <- eval (extract v_13120 224 256);
      store v_13119 (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13121 0 1)) (uvalueMInt (extract v_13121 1 9)) (uvalueMInt (extract v_13121 9 32))) v_13130) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13133 0 1)) (uvalueMInt (extract v_13133 1 9)) (uvalueMInt (extract v_13133 9 32))) v_13130) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13143 0 1)) (uvalueMInt (extract v_13143 1 9)) (uvalueMInt (extract v_13143 9 32))) v_13130) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13153 0 1)) (uvalueMInt (extract v_13153 1 9)) (uvalueMInt (extract v_13153 9 32))) v_13130) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13163 0 1)) (uvalueMInt (extract v_13163 1 9)) (uvalueMInt (extract v_13163 9 32))) v_13130) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13173 0 1)) (uvalueMInt (extract v_13173 1 9)) (uvalueMInt (extract v_13173 9 32))) v_13130) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13183 0 1)) (uvalueMInt (extract v_13183 1 9)) (uvalueMInt (extract v_13183 9 32))) v_13130) 16) (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13193 0 1)) (uvalueMInt (extract v_13193 1 9)) (uvalueMInt (extract v_13193 9 32))) v_13130) 16)))))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3136 : imm int) (v_3139 : reg (bv 128)) (v_3135 : Mem) => do
      v_13211 <- evaluateAddress v_3135;
      v_13212 <- getRegister v_3139;
      v_13213 <- eval (extract v_13212 0 32);
      v_13222 <- eval (uvalueMInt (handleImmediateWithSignExtend v_3136 8 8));
      v_13225 <- eval (extract v_13212 32 64);
      v_13235 <- eval (extract v_13212 64 96);
      v_13245 <- eval (extract v_13212 96 128);
      store v_13211 (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13213 0 1)) (uvalueMInt (extract v_13213 1 9)) (uvalueMInt (extract v_13213 9 32))) v_13222) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13225 0 1)) (uvalueMInt (extract v_13225 1 9)) (uvalueMInt (extract v_13225 9 32))) v_13222) 16) (concat (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13235 0 1)) (uvalueMInt (extract v_13235 1 9)) (uvalueMInt (extract v_13235 9 32))) v_13222) 16) (Float2MInt (Float2Half (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13245 0 1)) (uvalueMInt (extract v_13245 1 9)) (uvalueMInt (extract v_13245 9 32))) v_13222) 16)))) 8;
      pure ()
    pat_end
