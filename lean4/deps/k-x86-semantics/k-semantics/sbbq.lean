def sbbq1 : instruction :=
  definst "sbbq" $ do
    pattern fun (v_3272 : imm int) (v_3273 : reg (bv 64)) => do
      v_8608 <- getRegister cf;
      v_8610 <- eval (handleImmediateWithSignExtend v_3272 32 32);
      v_8611 <- eval (leanSignExtend v_8610 64);
      v_8613 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8611 (expression.bv_nat 64 18446744073709551615)));
      v_8616 <- getRegister v_3273;
      v_8618 <- eval (add (mux (eq v_8608 (expression.bv_nat 1 1)) v_8613 (add v_8613 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_8616));
      v_8623 <- eval (extract v_8618 1 2);
      v_8624 <- eval (extract v_8618 1 65);
      v_8635 <- eval (eq (bv_xor (extract v_8611 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3273) v_8624;
      setRegister of (mux (bit_and (eq v_8635 (eq (extract v_8616 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8635 (eq v_8623 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8618 57 65));
      setRegister af (bv_xor (bv_xor (extract v_8610 27 28) (extract v_8616 59 60)) (extract v_8618 60 61));
      setRegister zf (zeroFlag v_8624);
      setRegister sf v_8623;
      setRegister cf (mux (notBool_ (eq (extract v_8618 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3281 : reg (bv 64)) (v_3282 : reg (bv 64)) => do
      v_8655 <- getRegister cf;
      v_8657 <- getRegister v_3281;
      v_8659 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8657 (expression.bv_nat 64 18446744073709551615)));
      v_8662 <- getRegister v_3282;
      v_8664 <- eval (add (mux (eq v_8655 (expression.bv_nat 1 1)) v_8659 (add v_8659 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_8662));
      v_8669 <- eval (extract v_8664 1 2);
      v_8670 <- eval (extract v_8664 1 65);
      v_8680 <- eval (eq (bv_xor (extract v_8657 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3282) v_8670;
      setRegister of (mux (bit_and (eq v_8680 (eq (extract v_8662 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8680 (eq v_8669 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8664 57 65));
      setRegister af (bv_xor (extract (bv_xor v_8657 v_8662) 59 60) (extract v_8664 60 61));
      setRegister zf (zeroFlag v_8670);
      setRegister sf v_8669;
      setRegister cf (mux (notBool_ (eq (extract v_8664 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3286 : imm int) rax => do
      v_8696 <- getRegister cf;
      v_8698 <- eval (handleImmediateWithSignExtend v_3286 32 32);
      v_8699 <- eval (leanSignExtend v_8698 64);
      v_8701 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8699 (expression.bv_nat 64 18446744073709551615)));
      v_8704 <- getRegister rax;
      v_8706 <- eval (add (mux (eq v_8696 (expression.bv_nat 1 1)) v_8701 (add v_8701 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_8704));
      v_8711 <- eval (extract v_8706 1 2);
      v_8717 <- eval (extract v_8706 1 65);
      v_8723 <- eval (eq (bv_xor (extract v_8699 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister rax v_8717;
      setRegister of (mux (bit_and (eq v_8723 (eq (extract v_8704 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8723 (eq v_8711 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8706 57 65));
      setRegister zf (zeroFlag v_8717);
      setRegister af (bv_xor (bv_xor (extract v_8698 27 28) (extract v_8704 59 60)) (extract v_8706 60 61));
      setRegister sf v_8711;
      setRegister cf (mux (notBool_ (eq (extract v_8706 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 64)) => do
      v_13247 <- getRegister cf;
      v_13249 <- evaluateAddress v_3276;
      v_13250 <- load v_13249 8;
      v_13252 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13250 (expression.bv_nat 64 18446744073709551615)));
      v_13255 <- getRegister v_3277;
      v_13257 <- eval (add (mux (eq v_13247 (expression.bv_nat 1 1)) v_13252 (add v_13252 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_13255));
      v_13262 <- eval (extract v_13257 1 2);
      v_13263 <- eval (extract v_13257 1 65);
      v_13273 <- eval (eq (bv_xor (extract v_13250 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3277) v_13263;
      setRegister of (mux (bit_and (eq v_13273 (eq (extract v_13255 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13273 (eq v_13262 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13257 57 65));
      setRegister af (bv_xor (extract (bv_xor v_13250 v_13255) 59 60) (extract v_13257 60 61));
      setRegister zf (zeroFlag v_13263);
      setRegister sf v_13262;
      setRegister cf (mux (notBool_ (eq (extract v_13257 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3264 : imm int) (v_3263 : Mem) => do
      v_17716 <- evaluateAddress v_3263;
      v_17717 <- getRegister cf;
      v_17719 <- eval (handleImmediateWithSignExtend v_3264 32 32);
      v_17720 <- eval (leanSignExtend v_17719 64);
      v_17722 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17720 (expression.bv_nat 64 18446744073709551615)));
      v_17725 <- load v_17716 8;
      v_17727 <- eval (add (mux (eq v_17717 (expression.bv_nat 1 1)) v_17722 (add v_17722 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_17725));
      v_17728 <- eval (extract v_17727 1 65);
      store v_17716 v_17728 8;
      v_17734 <- eval (extract v_17727 1 2);
      v_17745 <- eval (eq (bv_xor (extract v_17720 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17745 (eq (extract v_17725 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17745 (eq v_17734 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17727 57 65));
      setRegister af (bv_xor (bv_xor (extract v_17719 27 28) (extract v_17725 59 60)) (extract v_17727 60 61));
      setRegister zf (zeroFlag v_17728);
      setRegister sf v_17734;
      setRegister cf (mux (notBool_ (eq (extract v_17727 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3268 : reg (bv 64)) (v_3267 : Mem) => do
      v_17760 <- evaluateAddress v_3267;
      v_17761 <- getRegister cf;
      v_17763 <- getRegister v_3268;
      v_17765 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17763 (expression.bv_nat 64 18446744073709551615)));
      v_17768 <- load v_17760 8;
      v_17770 <- eval (add (mux (eq v_17761 (expression.bv_nat 1 1)) v_17765 (add v_17765 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_17768));
      v_17771 <- eval (extract v_17770 1 65);
      store v_17760 v_17771 8;
      v_17777 <- eval (extract v_17770 1 2);
      v_17787 <- eval (eq (bv_xor (extract v_17763 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17787 (eq (extract v_17768 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17787 (eq v_17777 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17770 57 65));
      setRegister af (bv_xor (extract (bv_xor v_17763 v_17768) 59 60) (extract v_17770 60 61));
      setRegister zf (zeroFlag v_17771);
      setRegister sf v_17777;
      setRegister cf (mux (notBool_ (eq (extract v_17770 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
