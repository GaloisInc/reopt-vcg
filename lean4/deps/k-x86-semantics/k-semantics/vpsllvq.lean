def vpsllvq1 : instruction :=
  definst "vpsllvq" $ do
    pattern fun (v_3141 : reg (bv 128)) (v_3142 : reg (bv 128)) (v_3143 : reg (bv 128)) => do
      v_8274 <- getRegister v_3142;
      v_8275 <- eval (extract v_8274 0 64);
      v_8276 <- getRegister v_3141;
      v_8282 <- eval (extract v_8274 64 128);
      setRegister (lhs.of_reg v_3143) (concat (extract (shl v_8275 (uvalueMInt (extract v_8276 0 64))) 0 (bitwidthMInt v_8275)) (extract (shl v_8282 (uvalueMInt (extract v_8276 64 128))) 0 (bitwidthMInt v_8282)));
      pure ()
    pat_end;
    pattern fun (v_3152 : reg (bv 256)) (v_3153 : reg (bv 256)) (v_3154 : reg (bv 256)) => do
      v_8295 <- getRegister v_3153;
      v_8296 <- eval (extract v_8295 0 64);
      v_8297 <- getRegister v_3152;
      v_8303 <- eval (extract v_8295 64 128);
      v_8309 <- eval (extract v_8295 128 192);
      v_8315 <- eval (extract v_8295 192 256);
      setRegister (lhs.of_reg v_3154) (concat (extract (shl v_8296 (uvalueMInt (extract v_8297 0 64))) 0 (bitwidthMInt v_8296)) (concat (extract (shl v_8303 (uvalueMInt (extract v_8297 64 128))) 0 (bitwidthMInt v_8303)) (concat (extract (shl v_8309 (uvalueMInt (extract v_8297 128 192))) 0 (bitwidthMInt v_8309)) (extract (shl v_8315 (uvalueMInt (extract v_8297 192 256))) 0 (bitwidthMInt v_8315)))));
      pure ()
    pat_end;
    pattern fun (v_3138 : Mem) (v_3136 : reg (bv 128)) (v_3137 : reg (bv 128)) => do
      v_15123 <- getRegister v_3136;
      v_15124 <- eval (extract v_15123 0 64);
      v_15125 <- evaluateAddress v_3138;
      v_15126 <- load v_15125 16;
      v_15132 <- eval (extract v_15123 64 128);
      setRegister (lhs.of_reg v_3137) (concat (extract (shl v_15124 (uvalueMInt (extract v_15126 0 64))) 0 (bitwidthMInt v_15124)) (extract (shl v_15132 (uvalueMInt (extract v_15126 64 128))) 0 (bitwidthMInt v_15132)));
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3148 : reg (bv 256)) (v_3149 : reg (bv 256)) => do
      v_15140 <- getRegister v_3148;
      v_15141 <- eval (extract v_15140 0 64);
      v_15142 <- evaluateAddress v_3147;
      v_15143 <- load v_15142 32;
      v_15149 <- eval (extract v_15140 64 128);
      v_15155 <- eval (extract v_15140 128 192);
      v_15161 <- eval (extract v_15140 192 256);
      setRegister (lhs.of_reg v_3149) (concat (extract (shl v_15141 (uvalueMInt (extract v_15143 0 64))) 0 (bitwidthMInt v_15141)) (concat (extract (shl v_15149 (uvalueMInt (extract v_15143 64 128))) 0 (bitwidthMInt v_15149)) (concat (extract (shl v_15155 (uvalueMInt (extract v_15143 128 192))) 0 (bitwidthMInt v_15155)) (extract (shl v_15161 (uvalueMInt (extract v_15143 192 256))) 0 (bitwidthMInt v_15161)))));
      pure ()
    pat_end
