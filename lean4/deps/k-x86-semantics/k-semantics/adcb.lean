def adcb1 : instruction :=
  definst "adcb" $ do
    pattern fun (v_2379 : imm int) al => do
      v_3754 <- getRegister cf;
      v_3756 <- eval (handleImmediateWithSignExtend v_2379 8 8);
      v_3757 <- eval (concat (expression.bv_nat 1 0) v_3756);
      v_3760 <- getRegister rax;
      v_3763 <- eval (add (mux (eq v_3754 (expression.bv_nat 1 1)) (add v_3757 (expression.bv_nat 9 1)) v_3757) (concat (expression.bv_nat 1 0) (extract v_3760 56 64)));
      v_3765 <- eval (extract v_3763 1 2);
      v_3771 <- eval (extract v_3763 1 9);
      v_3775 <- eval (eq (extract v_3756 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_3760 0 56) v_3771);
      setRegister of (mux (bit_and (eq v_3775 (eq (extract v_3760 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_3775 (eq v_3765 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3771);
      setRegister zf (zeroFlag v_3771);
      setRegister af (bv_xor (bv_xor (extract v_3756 3 4) (extract v_3760 59 60)) (extract v_3763 4 5));
      setRegister sf v_3765;
      setRegister cf (extract v_3763 0 1);
      pure ()
    pat_end;
    pattern fun (v_2395 : imm int) (v_2398 : reg (bv 8)) => do
      v_3805 <- getRegister cf;
      v_3807 <- eval (handleImmediateWithSignExtend v_2395 8 8);
      v_3808 <- eval (concat (expression.bv_nat 1 0) v_3807);
      v_3811 <- getRegister v_2398;
      v_3813 <- eval (add (mux (eq v_3805 (expression.bv_nat 1 1)) (add v_3808 (expression.bv_nat 9 1)) v_3808) (concat (expression.bv_nat 1 0) v_3811));
      v_3815 <- eval (extract v_3813 1 2);
      v_3816 <- eval (extract v_3813 1 9);
      v_3824 <- eval (eq (extract v_3807 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2398) v_3816;
      setRegister of (mux (bit_and (eq v_3824 (eq (extract v_3811 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3824 (eq v_3815 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3816);
      setRegister af (bv_xor (extract (bv_xor v_3807 v_3811) 3 4) (extract v_3813 4 5));
      setRegister zf (zeroFlag v_3816);
      setRegister sf v_3815;
      setRegister cf (extract v_3813 0 1);
      pure ()
    pat_end;
    pattern fun (v_2406 : reg (bv 8)) (v_2407 : reg (bv 8)) => do
      v_3844 <- getRegister cf;
      v_3846 <- getRegister v_2406;
      v_3847 <- eval (concat (expression.bv_nat 1 0) v_3846);
      v_3850 <- getRegister v_2407;
      v_3852 <- eval (add (mux (eq v_3844 (expression.bv_nat 1 1)) (add v_3847 (expression.bv_nat 9 1)) v_3847) (concat (expression.bv_nat 1 0) v_3850));
      v_3854 <- eval (extract v_3852 1 2);
      v_3855 <- eval (extract v_3852 1 9);
      v_3863 <- eval (eq (extract v_3846 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2407) v_3855;
      setRegister of (mux (bit_and (eq v_3863 (eq (extract v_3850 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3863 (eq v_3854 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3855);
      setRegister af (bv_xor (extract (bv_xor v_3846 v_3850) 3 4) (extract v_3852 4 5));
      setRegister zf (zeroFlag v_3855);
      setRegister sf v_3854;
      setRegister cf (extract v_3852 0 1);
      pure ()
    pat_end;
    pattern fun (v_2414 : imm int) (v_2417 : reg (bv 8)) => do
      v_3914 <- getRegister cf;
      v_3916 <- eval (handleImmediateWithSignExtend v_2414 8 8);
      v_3917 <- eval (concat (expression.bv_nat 1 0) v_3916);
      v_3920 <- getRegister v_2417;
      v_3922 <- eval (add (mux (eq v_3914 (expression.bv_nat 1 1)) (add v_3917 (expression.bv_nat 9 1)) v_3917) (concat (expression.bv_nat 1 0) v_3920));
      v_3924 <- eval (extract v_3922 1 2);
      v_3929 <- eval (extract v_3922 1 9);
      v_3933 <- eval (eq (extract v_3916 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2417) v_3929;
      setRegister of (mux (bit_and (eq v_3933 (eq (extract v_3920 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3933 (eq v_3924 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3929);
      setRegister zf (zeroFlag v_3929);
      setRegister af (bv_xor (extract (bv_xor v_3916 v_3920) 3 4) (extract v_3922 4 5));
      setRegister sf v_3924;
      setRegister cf (extract v_3922 0 1);
      pure ()
    pat_end;
    pattern fun (v_2426 : reg (bv 8)) (v_2425 : reg (bv 8)) => do
      v_3953 <- getRegister cf;
      v_3955 <- getRegister v_2426;
      v_3956 <- eval (concat (expression.bv_nat 1 0) v_3955);
      v_3959 <- getRegister v_2425;
      v_3961 <- eval (add (mux (eq v_3953 (expression.bv_nat 1 1)) (add v_3956 (expression.bv_nat 9 1)) v_3956) (concat (expression.bv_nat 1 0) v_3959));
      v_3963 <- eval (extract v_3961 1 2);
      v_3968 <- eval (extract v_3961 1 9);
      v_3972 <- eval (eq (extract v_3955 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2425) v_3968;
      setRegister of (mux (bit_and (eq v_3972 (eq (extract v_3959 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3972 (eq v_3963 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3968);
      setRegister zf (zeroFlag v_3968);
      setRegister af (bv_xor (extract (bv_xor v_3955 v_3959) 3 4) (extract v_3961 4 5));
      setRegister sf v_3963;
      setRegister cf (extract v_3961 0 1);
      pure ()
    pat_end;
    pattern fun (v_2401 : Mem) (v_2402 : reg (bv 8)) => do
      v_8810 <- getRegister cf;
      v_8812 <- evaluateAddress v_2401;
      v_8813 <- load v_8812 1;
      v_8814 <- eval (concat (expression.bv_nat 1 0) v_8813);
      v_8817 <- getRegister v_2402;
      v_8819 <- eval (add (mux (eq v_8810 (expression.bv_nat 1 1)) (add v_8814 (expression.bv_nat 9 1)) v_8814) (concat (expression.bv_nat 1 0) v_8817));
      v_8821 <- eval (extract v_8819 1 2);
      v_8826 <- eval (extract v_8819 1 9);
      v_8830 <- eval (eq (extract v_8813 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2402) v_8826;
      setRegister of (mux (bit_and (eq v_8830 (eq (extract v_8817 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8830 (eq v_8821 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8826);
      setRegister zf (zeroFlag v_8826);
      setRegister af (bv_xor (extract (bv_xor v_8813 v_8817) 3 4) (extract v_8819 4 5));
      setRegister sf v_8821;
      setRegister cf (extract v_8819 0 1);
      pure ()
    pat_end;
    pattern fun (v_2383 : imm int) (v_2385 : Mem) => do
      v_10239 <- evaluateAddress v_2385;
      v_10240 <- getRegister cf;
      v_10242 <- eval (handleImmediateWithSignExtend v_2383 8 8);
      v_10243 <- eval (concat (expression.bv_nat 1 0) v_10242);
      v_10246 <- load v_10239 1;
      v_10248 <- eval (add (mux (eq v_10240 (expression.bv_nat 1 1)) (add v_10243 (expression.bv_nat 9 1)) v_10243) (concat (expression.bv_nat 1 0) v_10246));
      v_10249 <- eval (extract v_10248 1 9);
      store v_10239 v_10249 1;
      v_10252 <- eval (extract v_10248 1 2);
      v_10260 <- eval (eq (extract v_10242 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10260 (eq (extract v_10246 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10260 (eq v_10252 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10249);
      setRegister af (bv_xor (extract (bv_xor v_10242 v_10246) 3 4) (extract v_10248 4 5));
      setRegister zf (zeroFlag v_10249);
      setRegister sf v_10252;
      setRegister cf (extract v_10248 0 1);
      pure ()
    pat_end;
    pattern fun (v_2389 : reg (bv 8)) (v_2388 : Mem) => do
      v_10275 <- evaluateAddress v_2388;
      v_10276 <- getRegister cf;
      v_10278 <- getRegister v_2389;
      v_10279 <- eval (concat (expression.bv_nat 1 0) v_10278);
      v_10282 <- load v_10275 1;
      v_10284 <- eval (add (mux (eq v_10276 (expression.bv_nat 1 1)) (add v_10279 (expression.bv_nat 9 1)) v_10279) (concat (expression.bv_nat 1 0) v_10282));
      v_10285 <- eval (extract v_10284 1 9);
      store v_10275 v_10285 1;
      v_10288 <- eval (extract v_10284 1 2);
      v_10296 <- eval (eq (extract v_10278 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10296 (eq (extract v_10282 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10296 (eq v_10288 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10285);
      setRegister af (bv_xor (extract (bv_xor v_10278 v_10282) 3 4) (extract v_10284 4 5));
      setRegister zf (zeroFlag v_10285);
      setRegister sf v_10288;
      setRegister cf (extract v_10284 0 1);
      pure ()
    pat_end
