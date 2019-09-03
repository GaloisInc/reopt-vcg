def cmpl1 : instruction :=
  definst "cmpl" $ do
    pattern fun (v_3354 : imm int) eax => do
      v_5500 <- eval (handleImmediateWithSignExtend v_3354 32 32);
      v_5506 <- getRegister rax;
      v_5509 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5500 (mi (bitwidthMInt v_5500) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) (extract v_5506 32 64)));
      v_5514 <- eval (extract v_5509 1 2);
      v_5524 <- eval (extract v_5500 0 1);
      v_5528 <- eval (eq (bv_xor v_5524 (mi (bitwidthMInt v_5524) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5528 (eq (extract v_5506 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_5528 (eq v_5514 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5509 25 33));
      setRegister af (bv_xor (bv_xor (extract v_5500 27 28) (extract v_5506 59 60)) (extract v_5509 28 29));
      setRegister zf (zeroFlag (extract v_5509 1 33));
      setRegister sf v_5514;
      setRegister cf (mux (notBool_ (eq (extract v_5509 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3366 : imm int) (v_3367 : reg (bv 32)) => do
      v_5551 <- eval (handleImmediateWithSignExtend v_3366 32 32);
      v_5557 <- getRegister v_3367;
      v_5559 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5551 (mi (bitwidthMInt v_5551) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5557));
      v_5564 <- eval (extract v_5559 1 2);
      v_5573 <- eval (extract v_5551 0 1);
      v_5577 <- eval (eq (bv_xor v_5573 (mi (bitwidthMInt v_5573) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5577 (eq (extract v_5557 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5577 (eq v_5564 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5559 25 33));
      setRegister af (bv_xor (extract (bv_xor v_5551 v_5557) 27 28) (extract v_5559 28 29));
      setRegister zf (zeroFlag (extract v_5559 1 33));
      setRegister sf v_5564;
      setRegister cf (mux (notBool_ (eq (extract v_5559 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3375 : reg (bv 32)) (v_3376 : reg (bv 32)) => do
      v_5596 <- getRegister v_3375;
      v_5602 <- getRegister v_3376;
      v_5604 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5596 (mi (bitwidthMInt v_5596) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5602));
      v_5609 <- eval (extract v_5604 1 2);
      v_5618 <- eval (extract v_5596 0 1);
      v_5622 <- eval (eq (bv_xor v_5618 (mi (bitwidthMInt v_5618) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5622 (eq (extract v_5602 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5622 (eq v_5609 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5604 25 33));
      setRegister af (bv_xor (extract (bv_xor v_5596 v_5602) 27 28) (extract v_5604 28 29));
      setRegister zf (zeroFlag (extract v_5604 1 33));
      setRegister sf v_5609;
      setRegister cf (mux (notBool_ (eq (extract v_5604 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3358 : imm int) (v_3359 : Mem) => do
      v_8851 <- eval (handleImmediateWithSignExtend v_3358 32 32);
      v_8857 <- evaluateAddress v_3359;
      v_8858 <- load v_8857 4;
      v_8860 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8851 (mi (bitwidthMInt v_8851) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8858));
      v_8865 <- eval (extract v_8860 1 2);
      v_8874 <- eval (extract v_8851 0 1);
      v_8878 <- eval (eq (bv_xor v_8874 (mi (bitwidthMInt v_8874) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8878 (eq (extract v_8858 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8878 (eq v_8865 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8860 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8851 v_8858) 27 28) (extract v_8860 28 29));
      setRegister zf (zeroFlag (extract v_8860 1 33));
      setRegister sf v_8865;
      setRegister cf (mux (notBool_ (eq (extract v_8860 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3363 : reg (bv 32)) (v_3362 : Mem) => do
      v_8893 <- getRegister v_3363;
      v_8899 <- evaluateAddress v_3362;
      v_8900 <- load v_8899 4;
      v_8902 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8893 (mi (bitwidthMInt v_8893) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8900));
      v_8907 <- eval (extract v_8902 1 2);
      v_8916 <- eval (extract v_8893 0 1);
      v_8920 <- eval (eq (bv_xor v_8916 (mi (bitwidthMInt v_8916) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8920 (eq (extract v_8900 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8920 (eq v_8907 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8902 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8893 v_8900) 27 28) (extract v_8902 28 29));
      setRegister zf (zeroFlag (extract v_8902 1 33));
      setRegister sf v_8907;
      setRegister cf (mux (notBool_ (eq (extract v_8902 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3371 : Mem) (v_3372 : reg (bv 32)) => do
      v_8935 <- evaluateAddress v_3371;
      v_8936 <- load v_8935 4;
      v_8942 <- getRegister v_3372;
      v_8944 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8936 (mi (bitwidthMInt v_8936) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8942));
      v_8949 <- eval (extract v_8944 1 2);
      v_8958 <- eval (extract v_8936 0 1);
      v_8962 <- eval (eq (bv_xor v_8958 (mi (bitwidthMInt v_8958) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8962 (eq (extract v_8942 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8962 (eq v_8949 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8944 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8936 v_8942) 27 28) (extract v_8944 28 29));
      setRegister zf (zeroFlag (extract v_8944 1 33));
      setRegister sf v_8949;
      setRegister cf (mux (notBool_ (eq (extract v_8944 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
