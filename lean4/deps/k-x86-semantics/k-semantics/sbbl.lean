def sbbl1 : instruction :=
  definst "sbbl" $ do
    pattern fun (v_3238 : imm int) eax => do
      v_8463 <- getRegister cf;
      v_8465 <- eval (handleImmediateWithSignExtend v_3238 32 32);
      v_8467 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8465 (expression.bv_nat 32 4294967295)));
      v_8470 <- getRegister rax;
      v_8473 <- eval (add (mux (eq v_8463 (expression.bv_nat 1 1)) v_8467 (add v_8467 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) (extract v_8470 32 64)));
      v_8478 <- eval (extract v_8473 1 2);
      v_8484 <- eval (extract v_8473 1 33);
      v_8490 <- eval (eq (bv_xor (extract v_8465 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister eax v_8484;
      setRegister of (mux (bit_and (eq v_8490 (eq (extract v_8470 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_8490 (eq v_8478 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8473 25 33));
      setRegister zf (zeroFlag v_8484);
      setRegister af (bv_xor (bv_xor (extract v_8465 27 28) (extract v_8470 59 60)) (extract v_8473 28 29));
      setRegister sf v_8478;
      setRegister cf (mux (notBool_ (eq (extract v_8473 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3250 : imm int) (v_3251 : reg (bv 32)) => do
      v_8514 <- getRegister cf;
      v_8516 <- eval (handleImmediateWithSignExtend v_3250 32 32);
      v_8518 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8516 (expression.bv_nat 32 4294967295)));
      v_8521 <- getRegister v_3251;
      v_8523 <- eval (add (mux (eq v_8514 (expression.bv_nat 1 1)) v_8518 (add v_8518 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_8521));
      v_8528 <- eval (extract v_8523 1 2);
      v_8529 <- eval (extract v_8523 1 33);
      v_8539 <- eval (eq (bv_xor (extract v_8516 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3251) v_8529;
      setRegister of (mux (bit_and (eq v_8539 (eq (extract v_8521 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8539 (eq v_8528 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8523 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8516 v_8521) 27 28) (extract v_8523 28 29));
      setRegister zf (zeroFlag v_8529);
      setRegister sf v_8528;
      setRegister cf (mux (notBool_ (eq (extract v_8523 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3259 : reg (bv 32)) (v_3260 : reg (bv 32)) => do
      v_8559 <- getRegister cf;
      v_8561 <- getRegister v_3259;
      v_8563 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8561 (expression.bv_nat 32 4294967295)));
      v_8566 <- getRegister v_3260;
      v_8568 <- eval (add (mux (eq v_8559 (expression.bv_nat 1 1)) v_8563 (add v_8563 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_8566));
      v_8573 <- eval (extract v_8568 1 2);
      v_8574 <- eval (extract v_8568 1 33);
      v_8584 <- eval (eq (bv_xor (extract v_8561 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3260) v_8574;
      setRegister of (mux (bit_and (eq v_8584 (eq (extract v_8566 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8584 (eq v_8573 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8568 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8561 v_8566) 27 28) (extract v_8568 28 29));
      setRegister zf (zeroFlag v_8574);
      setRegister sf v_8573;
      setRegister cf (mux (notBool_ (eq (extract v_8568 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3254 : Mem) (v_3255 : reg (bv 32)) => do
      v_13203 <- getRegister cf;
      v_13205 <- evaluateAddress v_3254;
      v_13206 <- load v_13205 4;
      v_13208 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13206 (expression.bv_nat 32 4294967295)));
      v_13211 <- getRegister v_3255;
      v_13213 <- eval (add (mux (eq v_13203 (expression.bv_nat 1 1)) v_13208 (add v_13208 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_13211));
      v_13218 <- eval (extract v_13213 1 2);
      v_13219 <- eval (extract v_13213 1 33);
      v_13229 <- eval (eq (bv_xor (extract v_13206 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3255) v_13219;
      setRegister of (mux (bit_and (eq v_13229 (eq (extract v_13211 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13229 (eq v_13218 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13213 25 33));
      setRegister af (bv_xor (extract (bv_xor v_13206 v_13211) 27 28) (extract v_13213 28 29));
      setRegister zf (zeroFlag v_13219);
      setRegister sf v_13218;
      setRegister cf (mux (notBool_ (eq (extract v_13213 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3242 : imm int) (v_3241 : Mem) => do
      v_17632 <- evaluateAddress v_3241;
      v_17633 <- getRegister cf;
      v_17635 <- eval (handleImmediateWithSignExtend v_3242 32 32);
      v_17637 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17635 (expression.bv_nat 32 4294967295)));
      v_17640 <- load v_17632 4;
      v_17642 <- eval (add (mux (eq v_17633 (expression.bv_nat 1 1)) v_17637 (add v_17637 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_17640));
      v_17643 <- eval (extract v_17642 1 33);
      store v_17632 v_17643 4;
      v_17649 <- eval (extract v_17642 1 2);
      v_17659 <- eval (eq (bv_xor (extract v_17635 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17659 (eq (extract v_17640 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17659 (eq v_17649 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17642 25 33));
      setRegister af (bv_xor (extract (bv_xor v_17635 v_17640) 27 28) (extract v_17642 28 29));
      setRegister zf (zeroFlag v_17643);
      setRegister sf v_17649;
      setRegister cf (mux (notBool_ (eq (extract v_17642 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3246 : reg (bv 32)) (v_3245 : Mem) => do
      v_17674 <- evaluateAddress v_3245;
      v_17675 <- getRegister cf;
      v_17677 <- getRegister v_3246;
      v_17679 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17677 (expression.bv_nat 32 4294967295)));
      v_17682 <- load v_17674 4;
      v_17684 <- eval (add (mux (eq v_17675 (expression.bv_nat 1 1)) v_17679 (add v_17679 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_17682));
      v_17685 <- eval (extract v_17684 1 33);
      store v_17674 v_17685 4;
      v_17691 <- eval (extract v_17684 1 2);
      v_17701 <- eval (eq (bv_xor (extract v_17677 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17701 (eq (extract v_17682 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17701 (eq v_17691 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17684 25 33));
      setRegister af (bv_xor (extract (bv_xor v_17677 v_17682) 27 28) (extract v_17684 28 29));
      setRegister zf (zeroFlag v_17685);
      setRegister sf v_17691;
      setRegister cf (mux (notBool_ (eq (extract v_17684 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
