def sbbl1 : instruction :=
  definst "sbbl" $ do
    pattern fun (v_3226 : imm int) eax => do
      v_8505 <- getRegister cf;
      v_8507 <- eval (handleImmediateWithSignExtend v_3226 32 32);
      v_8511 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8507 (mi (bitwidthMInt v_8507) -1)));
      v_8514 <- getRegister rax;
      v_8517 <- eval (add (mux (eq v_8505 (expression.bv_nat 1 1)) v_8511 (add v_8511 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) (extract v_8514 32 64)));
      v_8522 <- eval (extract v_8517 1 2);
      v_8528 <- eval (extract v_8517 1 33);
      v_8532 <- eval (extract v_8507 0 1);
      v_8536 <- eval (eq (bv_xor v_8532 (mi (bitwidthMInt v_8532) -1)) (expression.bv_nat 1 1));
      setRegister eax v_8528;
      setRegister of (mux (bit_and (eq v_8536 (eq (extract v_8514 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_8536 (eq v_8522 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8517 25 33));
      setRegister zf (zeroFlag v_8528);
      setRegister af (bv_xor (bv_xor (extract v_8507 27 28) (extract v_8514 59 60)) (extract v_8517 28 29));
      setRegister sf v_8522;
      setRegister cf (mux (notBool_ (eq (extract v_8517 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3238 : imm int) (v_3239 : reg (bv 32)) => do
      v_8560 <- getRegister cf;
      v_8562 <- eval (handleImmediateWithSignExtend v_3238 32 32);
      v_8566 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8562 (mi (bitwidthMInt v_8562) -1)));
      v_8569 <- getRegister v_3239;
      v_8571 <- eval (add (mux (eq v_8560 (expression.bv_nat 1 1)) v_8566 (add v_8566 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_8569));
      v_8576 <- eval (extract v_8571 1 2);
      v_8581 <- eval (extract v_8571 1 33);
      v_8585 <- eval (extract v_8562 0 1);
      v_8589 <- eval (eq (bv_xor v_8585 (mi (bitwidthMInt v_8585) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3239) v_8581;
      setRegister of (mux (bit_and (eq v_8589 (eq (extract v_8569 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8589 (eq v_8576 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8571 25 33));
      setRegister zf (zeroFlag v_8581);
      setRegister af (bv_xor (extract (bv_xor v_8562 v_8569) 27 28) (extract v_8571 28 29));
      setRegister sf v_8576;
      setRegister cf (mux (notBool_ (eq (extract v_8571 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3247 : reg (bv 32)) (v_3248 : reg (bv 32)) => do
      v_8609 <- getRegister cf;
      v_8611 <- getRegister v_3247;
      v_8615 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8611 (mi (bitwidthMInt v_8611) -1)));
      v_8618 <- getRegister v_3248;
      v_8620 <- eval (add (mux (eq v_8609 (expression.bv_nat 1 1)) v_8615 (add v_8615 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_8618));
      v_8625 <- eval (extract v_8620 1 2);
      v_8630 <- eval (extract v_8620 1 33);
      v_8634 <- eval (extract v_8611 0 1);
      v_8638 <- eval (eq (bv_xor v_8634 (mi (bitwidthMInt v_8634) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3248) v_8630;
      setRegister of (mux (bit_and (eq v_8638 (eq (extract v_8618 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8638 (eq v_8625 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8620 25 33));
      setRegister zf (zeroFlag v_8630);
      setRegister af (bv_xor (extract (bv_xor v_8611 v_8618) 27 28) (extract v_8620 28 29));
      setRegister sf v_8625;
      setRegister cf (mux (notBool_ (eq (extract v_8620 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3241 : Mem) (v_3244 : reg (bv 32)) => do
      v_13289 <- getRegister cf;
      v_13291 <- evaluateAddress v_3241;
      v_13292 <- load v_13291 4;
      v_13296 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13292 (mi (bitwidthMInt v_13292) -1)));
      v_13299 <- getRegister v_3244;
      v_13301 <- eval (add (mux (eq v_13289 (expression.bv_nat 1 1)) v_13296 (add v_13296 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_13299));
      v_13306 <- eval (extract v_13301 1 2);
      v_13307 <- eval (extract v_13301 1 33);
      v_13315 <- eval (extract v_13292 0 1);
      v_13319 <- eval (eq (bv_xor v_13315 (mi (bitwidthMInt v_13315) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3244) v_13307;
      setRegister of (mux (bit_and (eq v_13319 (eq (extract v_13299 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13319 (eq v_13306 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13301 25 33));
      setRegister af (bv_xor (extract (bv_xor v_13292 v_13299) 27 28) (extract v_13301 28 29));
      setRegister zf (zeroFlag v_13307);
      setRegister sf v_13306;
      setRegister cf (mux (notBool_ (eq (extract v_13301 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3231 : imm int) (v_3228 : Mem) => do
      v_17878 <- evaluateAddress v_3228;
      v_17879 <- getRegister cf;
      v_17881 <- eval (handleImmediateWithSignExtend v_3231 32 32);
      v_17885 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17881 (mi (bitwidthMInt v_17881) -1)));
      v_17888 <- load v_17878 4;
      v_17890 <- eval (add (mux (eq v_17879 (expression.bv_nat 1 1)) v_17885 (add v_17885 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_17888));
      v_17891 <- eval (extract v_17890 1 33);
      store v_17878 v_17891 4;
      v_17897 <- eval (extract v_17890 1 2);
      v_17905 <- eval (extract v_17881 0 1);
      v_17909 <- eval (eq (bv_xor v_17905 (mi (bitwidthMInt v_17905) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17909 (eq (extract v_17888 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17909 (eq v_17897 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17890 25 33));
      setRegister af (bv_xor (extract (bv_xor v_17881 v_17888) 27 28) (extract v_17890 28 29));
      setRegister zf (zeroFlag v_17891);
      setRegister sf v_17897;
      setRegister cf (mux (notBool_ (eq (extract v_17890 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3235 : reg (bv 32)) (v_3232 : Mem) => do
      v_17924 <- evaluateAddress v_3232;
      v_17925 <- getRegister cf;
      v_17927 <- getRegister v_3235;
      v_17931 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17927 (mi (bitwidthMInt v_17927) -1)));
      v_17934 <- load v_17924 4;
      v_17936 <- eval (add (mux (eq v_17925 (expression.bv_nat 1 1)) v_17931 (add v_17931 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_17934));
      v_17937 <- eval (extract v_17936 1 33);
      store v_17924 v_17937 4;
      v_17943 <- eval (extract v_17936 1 2);
      v_17951 <- eval (extract v_17927 0 1);
      v_17955 <- eval (eq (bv_xor v_17951 (mi (bitwidthMInt v_17951) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17955 (eq (extract v_17934 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17955 (eq v_17943 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17936 25 33));
      setRegister af (bv_xor (extract (bv_xor v_17927 v_17934) 27 28) (extract v_17936 28 29));
      setRegister zf (zeroFlag v_17937);
      setRegister sf v_17943;
      setRegister cf (mux (notBool_ (eq (extract v_17936 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
