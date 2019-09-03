def sbbw1 : instruction :=
  definst "sbbw" $ do
    pattern fun (v_3290 : imm int) ax => do
      v_8739 <- getRegister cf;
      v_8741 <- eval (handleImmediateWithSignExtend v_3290 16 16);
      v_8743 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8741 (expression.bv_nat 16 65535)));
      v_8746 <- getRegister rax;
      v_8749 <- eval (add (mux (eq v_8739 (expression.bv_nat 1 1)) v_8743 (add v_8743 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) (extract v_8746 48 64)));
      v_8754 <- eval (extract v_8749 1 2);
      v_8760 <- eval (extract v_8749 1 17);
      v_8766 <- eval (eq (bv_xor (extract v_8741 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_8746 0 48) v_8760);
      setRegister of (mux (bit_and (eq v_8766 (eq (extract v_8746 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_8766 (eq v_8754 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8749 9 17));
      setRegister zf (zeroFlag v_8760);
      setRegister af (bv_xor (bv_xor (extract v_8741 11 12) (extract v_8746 59 60)) (extract v_8749 12 13));
      setRegister sf v_8754;
      setRegister cf (mux (notBool_ (eq (extract v_8749 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3302 : imm int) (v_3303 : reg (bv 16)) => do
      v_8792 <- getRegister cf;
      v_8794 <- eval (handleImmediateWithSignExtend v_3302 16 16);
      v_8796 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8794 (expression.bv_nat 16 65535)));
      v_8799 <- getRegister v_3303;
      v_8801 <- eval (add (mux (eq v_8792 (expression.bv_nat 1 1)) v_8796 (add v_8796 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_8799));
      v_8806 <- eval (extract v_8801 1 2);
      v_8811 <- eval (extract v_8801 1 17);
      v_8817 <- eval (eq (bv_xor (extract v_8794 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3303) v_8811;
      setRegister of (mux (bit_and (eq v_8817 (eq (extract v_8799 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8817 (eq v_8806 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8801 9 17));
      setRegister zf (zeroFlag v_8811);
      setRegister af (bv_xor (extract (bv_xor v_8794 v_8799) 11 12) (extract v_8801 12 13));
      setRegister sf v_8806;
      setRegister cf (mux (notBool_ (eq (extract v_8801 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3311 : reg (bv 16)) (v_3312 : reg (bv 16)) => do
      v_8837 <- getRegister cf;
      v_8839 <- getRegister v_3311;
      v_8841 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8839 (expression.bv_nat 16 65535)));
      v_8844 <- getRegister v_3312;
      v_8846 <- eval (add (mux (eq v_8837 (expression.bv_nat 1 1)) v_8841 (add v_8841 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_8844));
      v_8851 <- eval (extract v_8846 1 2);
      v_8856 <- eval (extract v_8846 1 17);
      v_8862 <- eval (eq (bv_xor (extract v_8839 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3312) v_8856;
      setRegister of (mux (bit_and (eq v_8862 (eq (extract v_8844 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8862 (eq v_8851 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8846 9 17));
      setRegister zf (zeroFlag v_8856);
      setRegister af (bv_xor (extract (bv_xor v_8839 v_8844) 11 12) (extract v_8846 12 13));
      setRegister sf v_8851;
      setRegister cf (mux (notBool_ (eq (extract v_8846 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3306 : Mem) (v_3307 : reg (bv 16)) => do
      v_13291 <- getRegister cf;
      v_13293 <- evaluateAddress v_3306;
      v_13294 <- load v_13293 2;
      v_13296 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13294 (expression.bv_nat 16 65535)));
      v_13299 <- getRegister v_3307;
      v_13301 <- eval (add (mux (eq v_13291 (expression.bv_nat 1 1)) v_13296 (add v_13296 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_13299));
      v_13306 <- eval (extract v_13301 1 2);
      v_13311 <- eval (extract v_13301 1 17);
      v_13317 <- eval (eq (bv_xor (extract v_13294 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3307) v_13311;
      setRegister of (mux (bit_and (eq v_13317 (eq (extract v_13299 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13317 (eq v_13306 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13301 9 17));
      setRegister zf (zeroFlag v_13311);
      setRegister af (bv_xor (extract (bv_xor v_13294 v_13299) 11 12) (extract v_13301 12 13));
      setRegister sf v_13306;
      setRegister cf (mux (notBool_ (eq (extract v_13301 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3294 : imm int) (v_3293 : Mem) => do
      v_17802 <- evaluateAddress v_3293;
      v_17803 <- getRegister cf;
      v_17805 <- eval (handleImmediateWithSignExtend v_3294 16 16);
      v_17807 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17805 (expression.bv_nat 16 65535)));
      v_17810 <- load v_17802 2;
      v_17812 <- eval (add (mux (eq v_17803 (expression.bv_nat 1 1)) v_17807 (add v_17807 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_17810));
      v_17813 <- eval (extract v_17812 1 17);
      store v_17802 v_17813 2;
      v_17819 <- eval (extract v_17812 1 2);
      v_17829 <- eval (eq (bv_xor (extract v_17805 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17829 (eq (extract v_17810 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17829 (eq v_17819 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17812 9 17));
      setRegister af (bv_xor (extract (bv_xor v_17805 v_17810) 11 12) (extract v_17812 12 13));
      setRegister zf (zeroFlag v_17813);
      setRegister sf v_17819;
      setRegister cf (mux (notBool_ (eq (extract v_17812 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3298 : reg (bv 16)) (v_3297 : Mem) => do
      v_17844 <- evaluateAddress v_3297;
      v_17845 <- getRegister cf;
      v_17847 <- getRegister v_3298;
      v_17849 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17847 (expression.bv_nat 16 65535)));
      v_17852 <- load v_17844 2;
      v_17854 <- eval (add (mux (eq v_17845 (expression.bv_nat 1 1)) v_17849 (add v_17849 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_17852));
      v_17855 <- eval (extract v_17854 1 17);
      store v_17844 v_17855 2;
      v_17861 <- eval (extract v_17854 1 2);
      v_17871 <- eval (eq (bv_xor (extract v_17847 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17871 (eq (extract v_17852 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17871 (eq v_17861 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17854 9 17));
      setRegister af (bv_xor (extract (bv_xor v_17847 v_17852) 11 12) (extract v_17854 12 13));
      setRegister zf (zeroFlag v_17855);
      setRegister sf v_17861;
      setRegister cf (mux (notBool_ (eq (extract v_17854 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
