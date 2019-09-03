def shlq1 : instruction :=
  definst "shlq" $ do
    pattern fun cl (v_2779 : reg (bv 64)) => do
      v_4984 <- getRegister rcx;
      v_4986 <- eval (bv_and (extract v_4984 56 64) (expression.bv_nat 8 63));
      v_4987 <- eval (uge v_4986 (expression.bv_nat 8 64));
      v_4990 <- eval (eq v_4986 (expression.bv_nat 8 0));
      v_4991 <- eval (notBool_ v_4990);
      v_4992 <- getRegister v_2779;
      v_4993 <- eval (concat (expression.bv_nat 1 0) v_4992);
      v_4998 <- eval (extract (shl v_4993 (uvalueMInt (concat (expression.bv_nat 57 0) v_4986))) 0 (bitwidthMInt v_4993));
      v_5002 <- getRegister cf;
      v_5007 <- eval (bit_or (bit_and v_4987 undef) (bit_and (notBool_ v_4987) (bit_or (bit_and v_4991 (eq (extract v_4998 0 1) (expression.bv_nat 1 1))) (bit_and v_4990 (eq v_5002 (expression.bv_nat 1 1))))));
      v_5010 <- eval (eq (extract v_4998 1 2) (expression.bv_nat 1 1));
      v_5012 <- getRegister sf;
      v_5017 <- eval (extract v_4998 1 65);
      v_5020 <- getRegister zf;
      v_5025 <- eval (bit_and v_4991 undef);
      v_5026 <- getRegister af;
      v_5061 <- getRegister pf;
      v_5066 <- eval (eq v_4986 (expression.bv_nat 8 1));
      v_5071 <- getRegister of;
      setRegister (lhs.of_reg v_2779) v_5017;
      setRegister of (mux (bit_or (bit_and v_5066 (notBool_ (eq v_5007 v_5010))) (bit_and (notBool_ v_5066) (bit_or v_5025 (bit_and v_4990 (eq v_5071 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4991 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4998 64 65) (expression.bv_nat 1 1)) (eq (extract v_4998 63 64) (expression.bv_nat 1 1)))) (eq (extract v_4998 62 63) (expression.bv_nat 1 1)))) (eq (extract v_4998 61 62) (expression.bv_nat 1 1)))) (eq (extract v_4998 60 61) (expression.bv_nat 1 1)))) (eq (extract v_4998 59 60) (expression.bv_nat 1 1)))) (eq (extract v_4998 58 59) (expression.bv_nat 1 1)))) (eq (extract v_4998 57 58) (expression.bv_nat 1 1)))) (bit_and v_4990 (eq v_5061 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5025 (bit_and v_4990 (eq v_5026 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4991 (eq v_5017 (expression.bv_nat 64 0))) (bit_and v_4990 (eq v_5020 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4991 v_5010) (bit_and v_4990 (eq v_5012 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5007 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2782 : imm int) (v_2784 : reg (bv 64)) => do
      v_5086 <- eval (bv_and (handleImmediateWithSignExtend v_2782 8 8) (expression.bv_nat 8 63));
      v_5087 <- eval (uge v_5086 (expression.bv_nat 8 64));
      v_5090 <- eval (eq v_5086 (expression.bv_nat 8 0));
      v_5091 <- eval (notBool_ v_5090);
      v_5092 <- getRegister v_2784;
      v_5093 <- eval (concat (expression.bv_nat 1 0) v_5092);
      v_5098 <- eval (extract (shl v_5093 (uvalueMInt (concat (expression.bv_nat 57 0) v_5086))) 0 (bitwidthMInt v_5093));
      v_5102 <- getRegister cf;
      v_5107 <- eval (bit_or (bit_and v_5087 undef) (bit_and (notBool_ v_5087) (bit_or (bit_and v_5091 (eq (extract v_5098 0 1) (expression.bv_nat 1 1))) (bit_and v_5090 (eq v_5102 (expression.bv_nat 1 1))))));
      v_5110 <- eval (eq (extract v_5098 1 2) (expression.bv_nat 1 1));
      v_5112 <- getRegister sf;
      v_5117 <- eval (extract v_5098 1 65);
      v_5120 <- getRegister zf;
      v_5125 <- eval (bit_and v_5091 undef);
      v_5126 <- getRegister af;
      v_5161 <- getRegister pf;
      v_5166 <- eval (eq v_5086 (expression.bv_nat 8 1));
      v_5171 <- getRegister of;
      setRegister (lhs.of_reg v_2784) v_5117;
      setRegister of (mux (bit_or (bit_and v_5166 (notBool_ (eq v_5107 v_5110))) (bit_and (notBool_ v_5166) (bit_or v_5125 (bit_and v_5090 (eq v_5171 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5091 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5098 64 65) (expression.bv_nat 1 1)) (eq (extract v_5098 63 64) (expression.bv_nat 1 1)))) (eq (extract v_5098 62 63) (expression.bv_nat 1 1)))) (eq (extract v_5098 61 62) (expression.bv_nat 1 1)))) (eq (extract v_5098 60 61) (expression.bv_nat 1 1)))) (eq (extract v_5098 59 60) (expression.bv_nat 1 1)))) (eq (extract v_5098 58 59) (expression.bv_nat 1 1)))) (eq (extract v_5098 57 58) (expression.bv_nat 1 1)))) (bit_and v_5090 (eq v_5161 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5125 (bit_and v_5090 (eq v_5126 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5091 (eq v_5117 (expression.bv_nat 64 0))) (bit_and v_5090 (eq v_5120 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5091 v_5110) (bit_and v_5090 (eq v_5112 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5107 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2788 : reg (bv 64)) => do
      v_5185 <- getRegister v_2788;
      v_5186 <- eval (concat (expression.bv_nat 1 0) v_5185);
      v_5189 <- eval (extract (shl v_5186 1) 0 (bitwidthMInt v_5186));
      v_5190 <- eval (extract v_5189 0 1);
      v_5191 <- eval (extract v_5189 1 2);
      v_5192 <- eval (extract v_5189 1 65);
      setRegister (lhs.of_reg v_2788) v_5192;
      setRegister of (mux (notBool_ (eq (eq v_5190 (expression.bv_nat 1 1)) (eq v_5191 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5189 57 65));
      setRegister af undef;
      setRegister zf (zeroFlag v_5192);
      setRegister sf v_5191;
      setRegister cf v_5190;
      pure ()
    pat_end;
    pattern fun cl (v_2768 : Mem) => do
      v_11175 <- evaluateAddress v_2768;
      v_11176 <- load v_11175 8;
      v_11177 <- eval (concat (expression.bv_nat 1 0) v_11176);
      v_11178 <- getRegister rcx;
      v_11180 <- eval (bv_and (extract v_11178 56 64) (expression.bv_nat 8 63));
      v_11185 <- eval (extract (shl v_11177 (uvalueMInt (concat (expression.bv_nat 57 0) v_11180))) 0 (bitwidthMInt v_11177));
      v_11186 <- eval (extract v_11185 1 65);
      store v_11175 v_11186 8;
      v_11188 <- eval (uge v_11180 (expression.bv_nat 8 64));
      v_11191 <- eval (eq v_11180 (expression.bv_nat 8 0));
      v_11192 <- eval (notBool_ v_11191);
      v_11196 <- getRegister cf;
      v_11201 <- eval (bit_or (bit_and v_11188 undef) (bit_and (notBool_ v_11188) (bit_or (bit_and v_11192 (eq (extract v_11185 0 1) (expression.bv_nat 1 1))) (bit_and v_11191 (eq v_11196 (expression.bv_nat 1 1))))));
      v_11204 <- eval (eq (extract v_11185 1 2) (expression.bv_nat 1 1));
      v_11206 <- getRegister sf;
      v_11213 <- getRegister zf;
      v_11218 <- eval (bit_and v_11192 undef);
      v_11219 <- getRegister af;
      v_11254 <- getRegister pf;
      v_11259 <- eval (eq v_11180 (expression.bv_nat 8 1));
      v_11264 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11259 (notBool_ (eq v_11201 v_11204))) (bit_and (notBool_ v_11259) (bit_or v_11218 (bit_and v_11191 (eq v_11264 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11192 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11185 64 65) (expression.bv_nat 1 1)) (eq (extract v_11185 63 64) (expression.bv_nat 1 1)))) (eq (extract v_11185 62 63) (expression.bv_nat 1 1)))) (eq (extract v_11185 61 62) (expression.bv_nat 1 1)))) (eq (extract v_11185 60 61) (expression.bv_nat 1 1)))) (eq (extract v_11185 59 60) (expression.bv_nat 1 1)))) (eq (extract v_11185 58 59) (expression.bv_nat 1 1)))) (eq (extract v_11185 57 58) (expression.bv_nat 1 1)))) (bit_and v_11191 (eq v_11254 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11218 (bit_and v_11191 (eq v_11219 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11192 (eq v_11186 (expression.bv_nat 64 0))) (bit_and v_11191 (eq v_11213 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11192 v_11204) (bit_and v_11191 (eq v_11206 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11201 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2771 : imm int) (v_2772 : Mem) => do
      v_11277 <- evaluateAddress v_2772;
      v_11278 <- load v_11277 8;
      v_11279 <- eval (concat (expression.bv_nat 1 0) v_11278);
      v_11281 <- eval (bv_and (handleImmediateWithSignExtend v_2771 8 8) (expression.bv_nat 8 63));
      v_11286 <- eval (extract (shl v_11279 (uvalueMInt (concat (expression.bv_nat 57 0) v_11281))) 0 (bitwidthMInt v_11279));
      v_11287 <- eval (extract v_11286 1 65);
      store v_11277 v_11287 8;
      v_11289 <- eval (uge v_11281 (expression.bv_nat 8 64));
      v_11292 <- eval (eq v_11281 (expression.bv_nat 8 0));
      v_11293 <- eval (notBool_ v_11292);
      v_11297 <- getRegister cf;
      v_11302 <- eval (bit_or (bit_and v_11289 undef) (bit_and (notBool_ v_11289) (bit_or (bit_and v_11293 (eq (extract v_11286 0 1) (expression.bv_nat 1 1))) (bit_and v_11292 (eq v_11297 (expression.bv_nat 1 1))))));
      v_11305 <- eval (eq (extract v_11286 1 2) (expression.bv_nat 1 1));
      v_11307 <- getRegister sf;
      v_11314 <- getRegister zf;
      v_11319 <- eval (bit_and v_11293 undef);
      v_11320 <- getRegister af;
      v_11355 <- getRegister pf;
      v_11360 <- eval (eq v_11281 (expression.bv_nat 8 1));
      v_11365 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11360 (notBool_ (eq v_11302 v_11305))) (bit_and (notBool_ v_11360) (bit_or v_11319 (bit_and v_11292 (eq v_11365 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11293 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11286 64 65) (expression.bv_nat 1 1)) (eq (extract v_11286 63 64) (expression.bv_nat 1 1)))) (eq (extract v_11286 62 63) (expression.bv_nat 1 1)))) (eq (extract v_11286 61 62) (expression.bv_nat 1 1)))) (eq (extract v_11286 60 61) (expression.bv_nat 1 1)))) (eq (extract v_11286 59 60) (expression.bv_nat 1 1)))) (eq (extract v_11286 58 59) (expression.bv_nat 1 1)))) (eq (extract v_11286 57 58) (expression.bv_nat 1 1)))) (bit_and v_11292 (eq v_11355 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11319 (bit_and v_11292 (eq v_11320 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11293 (eq v_11287 (expression.bv_nat 64 0))) (bit_and v_11292 (eq v_11314 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11293 v_11305) (bit_and v_11292 (eq v_11307 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11302 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
