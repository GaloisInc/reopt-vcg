def salq1 : instruction :=
  definst "salq" $ do
    pattern fun cl (v_3018 : reg (bv 64)) => do
      v_6082 <- getRegister rcx;
      v_6084 <- eval (bv_and (extract v_6082 56 64) (expression.bv_nat 8 63));
      v_6085 <- eval (eq v_6084 (expression.bv_nat 8 0));
      v_6086 <- eval (notBool_ v_6085);
      v_6087 <- getRegister v_3018;
      v_6091 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6087) (concat (expression.bv_nat 57 0) v_6084)) 0 65);
      v_6092 <- eval (extract v_6091 1 65);
      v_6095 <- getRegister zf;
      v_6099 <- eval (isBitSet v_6091 1);
      v_6101 <- getRegister sf;
      v_6108 <- getRegister pf;
      v_6112 <- eval (eq v_6084 (expression.bv_nat 8 1));
      v_6113 <- eval (uge v_6084 (expression.bv_nat 8 64));
      v_6118 <- getRegister cf;
      v_6123 <- eval (bit_or (bit_and v_6113 undef) (bit_and (notBool_ v_6113) (bit_or (bit_and v_6086 (isBitSet v_6091 0)) (bit_and v_6085 (eq v_6118 (expression.bv_nat 1 1))))));
      v_6128 <- eval (bit_and v_6086 undef);
      v_6129 <- getRegister of;
      v_6135 <- getRegister af;
      setRegister (lhs.of_reg v_3018) v_6092;
      setRegister af (bit_or v_6128 (bit_and v_6085 (eq v_6135 (expression.bv_nat 1 1))));
      setRegister cf v_6123;
      setRegister of (bit_or (bit_and v_6112 (notBool_ (eq v_6123 v_6099))) (bit_and (notBool_ v_6112) (bit_or v_6128 (bit_and v_6085 (eq v_6129 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_6086 (parityFlag (extract v_6091 57 65))) (bit_and v_6085 (eq v_6108 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6086 v_6099) (bit_and v_6085 (eq v_6101 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6086 (eq v_6092 (expression.bv_nat 64 0))) (bit_and v_6085 (eq v_6095 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3021 : imm int) (v_3023 : reg (bv 64)) => do
      v_6147 <- eval (bv_and (handleImmediateWithSignExtend v_3021 8 8) (expression.bv_nat 8 63));
      v_6148 <- eval (eq v_6147 (expression.bv_nat 8 0));
      v_6149 <- eval (notBool_ v_6148);
      v_6150 <- getRegister v_3023;
      v_6154 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6150) (concat (expression.bv_nat 57 0) v_6147)) 0 65);
      v_6155 <- eval (extract v_6154 1 65);
      v_6158 <- getRegister zf;
      v_6162 <- eval (isBitSet v_6154 1);
      v_6164 <- getRegister sf;
      v_6171 <- getRegister pf;
      v_6175 <- eval (eq v_6147 (expression.bv_nat 8 1));
      v_6176 <- eval (uge v_6147 (expression.bv_nat 8 64));
      v_6181 <- getRegister cf;
      v_6186 <- eval (bit_or (bit_and v_6176 undef) (bit_and (notBool_ v_6176) (bit_or (bit_and v_6149 (isBitSet v_6154 0)) (bit_and v_6148 (eq v_6181 (expression.bv_nat 1 1))))));
      v_6191 <- eval (bit_and v_6149 undef);
      v_6192 <- getRegister of;
      v_6198 <- getRegister af;
      setRegister (lhs.of_reg v_3023) v_6155;
      setRegister af (bit_or v_6191 (bit_and v_6148 (eq v_6198 (expression.bv_nat 1 1))));
      setRegister cf v_6186;
      setRegister of (bit_or (bit_and v_6175 (notBool_ (eq v_6186 v_6162))) (bit_and (notBool_ v_6175) (bit_or v_6191 (bit_and v_6148 (eq v_6192 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_6149 (parityFlag (extract v_6154 57 65))) (bit_and v_6148 (eq v_6171 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6149 v_6162) (bit_and v_6148 (eq v_6164 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6149 (eq v_6155 (expression.bv_nat 64 0))) (bit_and v_6148 (eq v_6158 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3026 : reg (bv 64)) => do
      v_8313 <- getRegister v_3026;
      v_8316 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8313) (expression.bv_nat 65 1)) 0 65);
      v_8317 <- eval (extract v_8316 1 65);
      v_8319 <- eval (isBitSet v_8316 1);
      v_8322 <- eval (isBitSet v_8316 0);
      setRegister (lhs.of_reg v_3026) v_8317;
      setRegister af undef;
      setRegister cf v_8322;
      setRegister of (notBool_ (eq v_8322 v_8319));
      setRegister pf (parityFlag (extract v_8316 57 65));
      setRegister sf v_8319;
      setRegister zf (zeroFlag v_8317);
      pure ()
    pat_end;
    pattern fun cl (v_3004 : Mem) => do
      v_13215 <- evaluateAddress v_3004;
      v_13216 <- load v_13215 8;
      v_13218 <- getRegister rcx;
      v_13220 <- eval (bv_and (extract v_13218 56 64) (expression.bv_nat 8 63));
      v_13223 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13216) (concat (expression.bv_nat 57 0) v_13220)) 0 65);
      v_13224 <- eval (extract v_13223 1 65);
      store v_13215 v_13224 8;
      v_13226 <- eval (eq v_13220 (expression.bv_nat 8 0));
      v_13227 <- eval (notBool_ v_13226);
      v_13230 <- getRegister zf;
      v_13234 <- eval (isBitSet v_13223 1);
      v_13236 <- getRegister sf;
      v_13243 <- getRegister pf;
      v_13247 <- eval (eq v_13220 (expression.bv_nat 8 1));
      v_13248 <- eval (uge v_13220 (expression.bv_nat 8 64));
      v_13253 <- getRegister cf;
      v_13258 <- eval (bit_or (bit_and v_13248 undef) (bit_and (notBool_ v_13248) (bit_or (bit_and v_13227 (isBitSet v_13223 0)) (bit_and v_13226 (eq v_13253 (expression.bv_nat 1 1))))));
      v_13263 <- eval (bit_and v_13227 undef);
      v_13264 <- getRegister of;
      v_13270 <- getRegister af;
      setRegister af (bit_or v_13263 (bit_and v_13226 (eq v_13270 (expression.bv_nat 1 1))));
      setRegister cf v_13258;
      setRegister of (bit_or (bit_and v_13247 (notBool_ (eq v_13258 v_13234))) (bit_and (notBool_ v_13247) (bit_or v_13263 (bit_and v_13226 (eq v_13264 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_13227 (parityFlag (extract v_13223 57 65))) (bit_and v_13226 (eq v_13243 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13227 v_13234) (bit_and v_13226 (eq v_13236 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13227 (eq v_13224 (expression.bv_nat 64 0))) (bit_and v_13226 (eq v_13230 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3007 : imm int) (v_3008 : Mem) => do
      v_13280 <- evaluateAddress v_3008;
      v_13281 <- load v_13280 8;
      v_13284 <- eval (bv_and (handleImmediateWithSignExtend v_3007 8 8) (expression.bv_nat 8 63));
      v_13287 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13281) (concat (expression.bv_nat 57 0) v_13284)) 0 65);
      v_13288 <- eval (extract v_13287 1 65);
      store v_13280 v_13288 8;
      v_13290 <- eval (eq v_13284 (expression.bv_nat 8 0));
      v_13291 <- eval (notBool_ v_13290);
      v_13294 <- getRegister zf;
      v_13298 <- eval (isBitSet v_13287 1);
      v_13300 <- getRegister sf;
      v_13307 <- getRegister pf;
      v_13311 <- eval (eq v_13284 (expression.bv_nat 8 1));
      v_13312 <- eval (uge v_13284 (expression.bv_nat 8 64));
      v_13317 <- getRegister cf;
      v_13322 <- eval (bit_or (bit_and v_13312 undef) (bit_and (notBool_ v_13312) (bit_or (bit_and v_13291 (isBitSet v_13287 0)) (bit_and v_13290 (eq v_13317 (expression.bv_nat 1 1))))));
      v_13327 <- eval (bit_and v_13291 undef);
      v_13328 <- getRegister of;
      v_13334 <- getRegister af;
      setRegister af (bit_or v_13327 (bit_and v_13290 (eq v_13334 (expression.bv_nat 1 1))));
      setRegister cf v_13322;
      setRegister of (bit_or (bit_and v_13311 (notBool_ (eq v_13322 v_13298))) (bit_and (notBool_ v_13311) (bit_or v_13327 (bit_and v_13290 (eq v_13328 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_13291 (parityFlag (extract v_13287 57 65))) (bit_and v_13290 (eq v_13307 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13291 v_13298) (bit_and v_13290 (eq v_13300 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13291 (eq v_13288 (expression.bv_nat 64 0))) (bit_and v_13290 (eq v_13294 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3011 : Mem) => do
      v_14530 <- evaluateAddress v_3011;
      v_14531 <- load v_14530 8;
      v_14534 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_14531) (expression.bv_nat 65 1)) 0 65);
      v_14535 <- eval (extract v_14534 1 65);
      store v_14530 v_14535 8;
      v_14538 <- eval (isBitSet v_14534 1);
      v_14541 <- eval (isBitSet v_14534 0);
      setRegister af undef;
      setRegister cf v_14541;
      setRegister of (notBool_ (eq v_14541 v_14538));
      setRegister pf (parityFlag (extract v_14534 57 65));
      setRegister sf v_14538;
      setRegister zf (zeroFlag v_14535);
      pure ()
    pat_end
