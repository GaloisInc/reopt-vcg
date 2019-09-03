def salb1 : instruction :=
  definst "salb" $ do
    pattern fun cl (v_2880 : reg (bv 8)) => do
      v_5869 <- getRegister rcx;
      v_5871 <- eval (bv_and (extract v_5869 56 64) (expression.bv_nat 8 31));
      v_5872 <- eval (uge v_5871 (expression.bv_nat 8 8));
      v_5875 <- eval (eq v_5871 (expression.bv_nat 8 0));
      v_5876 <- eval (notBool_ v_5875);
      v_5877 <- getRegister v_2880;
      v_5878 <- eval (concat (expression.bv_nat 1 0) v_5877);
      v_5883 <- eval (extract (shl v_5878 (uvalueMInt (concat (expression.bv_nat 1 0) v_5871))) 0 (bitwidthMInt v_5878));
      v_5887 <- getRegister cf;
      v_5892 <- eval (bit_or (bit_and v_5872 undef) (bit_and (notBool_ v_5872) (bit_or (bit_and v_5876 (eq (extract v_5883 0 1) (expression.bv_nat 1 1))) (bit_and v_5875 (eq v_5887 (expression.bv_nat 1 1))))));
      v_5895 <- eval (eq (extract v_5883 1 2) (expression.bv_nat 1 1));
      v_5897 <- getRegister sf;
      v_5902 <- eval (bit_and v_5876 undef);
      v_5903 <- getRegister af;
      v_5908 <- eval (extract v_5883 1 9);
      v_5911 <- getRegister zf;
      v_5944 <- getRegister pf;
      v_5949 <- eval (eq v_5871 (expression.bv_nat 8 1));
      v_5954 <- getRegister of;
      setRegister (lhs.of_reg v_2880) v_5908;
      setRegister of (mux (bit_or (bit_and v_5949 (notBool_ (eq v_5892 v_5895))) (bit_and (notBool_ v_5949) (bit_or v_5902 (bit_and v_5875 (eq v_5954 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5876 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5883 8 9) (expression.bv_nat 1 1)) (eq (extract v_5883 7 8) (expression.bv_nat 1 1)))) (eq (extract v_5883 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5883 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5883 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5883 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5883 2 3) (expression.bv_nat 1 1)))) v_5895)) (bit_and v_5875 (eq v_5944 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5876 (eq v_5908 (expression.bv_nat 8 0))) (bit_and v_5875 (eq v_5911 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5902 (bit_and v_5875 (eq v_5903 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5876 v_5895) (bit_and v_5875 (eq v_5897 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5892 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2881 : imm int) (v_2885 : reg (bv 8)) => do
      v_5969 <- eval (bv_and (handleImmediateWithSignExtend v_2881 8 8) (expression.bv_nat 8 31));
      v_5970 <- eval (uge v_5969 (expression.bv_nat 8 8));
      v_5973 <- eval (eq v_5969 (expression.bv_nat 8 0));
      v_5974 <- eval (notBool_ v_5973);
      v_5975 <- getRegister v_2885;
      v_5976 <- eval (concat (expression.bv_nat 1 0) v_5975);
      v_5981 <- eval (extract (shl v_5976 (uvalueMInt (concat (expression.bv_nat 1 0) v_5969))) 0 (bitwidthMInt v_5976));
      v_5985 <- getRegister cf;
      v_5990 <- eval (bit_or (bit_and v_5970 undef) (bit_and (notBool_ v_5970) (bit_or (bit_and v_5974 (eq (extract v_5981 0 1) (expression.bv_nat 1 1))) (bit_and v_5973 (eq v_5985 (expression.bv_nat 1 1))))));
      v_5993 <- eval (eq (extract v_5981 1 2) (expression.bv_nat 1 1));
      v_5995 <- getRegister sf;
      v_6000 <- eval (bit_and v_5974 undef);
      v_6001 <- getRegister af;
      v_6006 <- eval (extract v_5981 1 9);
      v_6009 <- getRegister zf;
      v_6042 <- getRegister pf;
      v_6047 <- eval (eq v_5969 (expression.bv_nat 8 1));
      v_6052 <- getRegister of;
      setRegister (lhs.of_reg v_2885) v_6006;
      setRegister of (mux (bit_or (bit_and v_6047 (notBool_ (eq v_5990 v_5993))) (bit_and (notBool_ v_6047) (bit_or v_6000 (bit_and v_5973 (eq v_6052 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5974 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5981 8 9) (expression.bv_nat 1 1)) (eq (extract v_5981 7 8) (expression.bv_nat 1 1)))) (eq (extract v_5981 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5981 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5981 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5981 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5981 2 3) (expression.bv_nat 1 1)))) v_5993)) (bit_and v_5973 (eq v_6042 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5974 (eq v_6006 (expression.bv_nat 8 0))) (bit_and v_5973 (eq v_6009 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6000 (bit_and v_5973 (eq v_6001 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5974 v_5993) (bit_and v_5973 (eq v_5995 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5990 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2892 : reg (bv 8)) => do
      v_6068 <- getRegister v_2892;
      v_6069 <- eval (concat (expression.bv_nat 1 0) v_6068);
      v_6072 <- eval (extract (shl v_6069 1) 0 (bitwidthMInt v_6069));
      v_6073 <- eval (extract v_6072 0 1);
      v_6074 <- eval (extract v_6072 1 2);
      v_6075 <- eval (extract v_6072 1 9);
      setRegister (lhs.of_reg v_2892) v_6075;
      setRegister of (mux (notBool_ (eq (eq v_6073 (expression.bv_nat 1 1)) (eq v_6074 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6075);
      setRegister zf (zeroFlag v_6075);
      setRegister af undef;
      setRegister sf v_6074;
      setRegister cf v_6073;
      pure ()
    pat_end;
    pattern fun (v_2888 : reg (bv 8)) => do
      v_9394 <- getRegister v_2888;
      v_9395 <- eval (concat (expression.bv_nat 1 0) v_9394);
      v_9398 <- eval (extract (shl v_9395 1) 0 (bitwidthMInt v_9395));
      v_9400 <- eval (eq (extract v_9398 0 1) (expression.bv_nat 1 1));
      v_9403 <- eval (eq (extract v_9398 1 2) (expression.bv_nat 1 1));
      v_9405 <- eval (extract v_9398 1 9);
      setRegister (lhs.of_reg v_2888) v_9405;
      setRegister of (mux (notBool_ (eq v_9400 v_9403)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9405);
      setRegister zf (zeroFlag v_9405);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux v_9403 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9400 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2888 : reg (bv 8)) => do
      v_9418 <- getRegister v_2888;
      v_9419 <- eval (concat (expression.bv_nat 1 0) v_9418);
      v_9422 <- eval (extract (shl v_9419 1) 0 (bitwidthMInt v_9419));
      v_9423 <- eval (extract v_9422 0 1);
      v_9424 <- eval (extract v_9422 1 2);
      v_9425 <- eval (extract v_9422 1 9);
      setRegister (lhs.of_reg v_2888) v_9425;
      setRegister of (mux (notBool_ (eq (eq v_9423 (expression.bv_nat 1 1)) (eq v_9424 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9425);
      setRegister zf (zeroFlag v_9425);
      setRegister af undef;
      setRegister sf v_9424;
      setRegister cf v_9423;
      pure ()
    pat_end;
    pattern fun cl (v_2864 : Mem) => do
      v_15411 <- evaluateAddress v_2864;
      v_15412 <- load v_15411 1;
      v_15413 <- eval (concat (expression.bv_nat 1 0) v_15412);
      v_15414 <- getRegister rcx;
      v_15416 <- eval (bv_and (extract v_15414 56 64) (expression.bv_nat 8 31));
      v_15421 <- eval (extract (shl v_15413 (uvalueMInt (concat (expression.bv_nat 1 0) v_15416))) 0 (bitwidthMInt v_15413));
      v_15422 <- eval (extract v_15421 1 9);
      store v_15411 v_15422 1;
      v_15424 <- eval (uge v_15416 (expression.bv_nat 8 8));
      v_15427 <- eval (eq v_15416 (expression.bv_nat 8 0));
      v_15428 <- eval (notBool_ v_15427);
      v_15432 <- getRegister cf;
      v_15437 <- eval (bit_or (bit_and v_15424 undef) (bit_and (notBool_ v_15424) (bit_or (bit_and v_15428 (eq (extract v_15421 0 1) (expression.bv_nat 1 1))) (bit_and v_15427 (eq v_15432 (expression.bv_nat 1 1))))));
      v_15440 <- eval (eq (extract v_15421 1 2) (expression.bv_nat 1 1));
      v_15442 <- getRegister sf;
      v_15449 <- getRegister zf;
      v_15454 <- eval (bit_and v_15428 undef);
      v_15455 <- getRegister af;
      v_15488 <- getRegister pf;
      v_15493 <- eval (eq v_15416 (expression.bv_nat 8 1));
      v_15498 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15493 (notBool_ (eq v_15437 v_15440))) (bit_and (notBool_ v_15493) (bit_or v_15454 (bit_and v_15427 (eq v_15498 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15428 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15421 8 9) (expression.bv_nat 1 1)) (eq (extract v_15421 7 8) (expression.bv_nat 1 1)))) (eq (extract v_15421 6 7) (expression.bv_nat 1 1)))) (eq (extract v_15421 5 6) (expression.bv_nat 1 1)))) (eq (extract v_15421 4 5) (expression.bv_nat 1 1)))) (eq (extract v_15421 3 4) (expression.bv_nat 1 1)))) (eq (extract v_15421 2 3) (expression.bv_nat 1 1)))) v_15440)) (bit_and v_15427 (eq v_15488 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15454 (bit_and v_15427 (eq v_15455 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15428 (eq v_15422 (expression.bv_nat 8 0))) (bit_and v_15427 (eq v_15449 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15428 v_15440) (bit_and v_15427 (eq v_15442 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15437 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2867 : imm int) (v_2868 : Mem) => do
      v_15511 <- evaluateAddress v_2868;
      v_15512 <- load v_15511 1;
      v_15513 <- eval (concat (expression.bv_nat 1 0) v_15512);
      v_15515 <- eval (bv_and (handleImmediateWithSignExtend v_2867 8 8) (expression.bv_nat 8 31));
      v_15520 <- eval (extract (shl v_15513 (uvalueMInt (concat (expression.bv_nat 1 0) v_15515))) 0 (bitwidthMInt v_15513));
      v_15521 <- eval (extract v_15520 1 9);
      store v_15511 v_15521 1;
      v_15523 <- eval (uge v_15515 (expression.bv_nat 8 8));
      v_15526 <- eval (eq v_15515 (expression.bv_nat 8 0));
      v_15527 <- eval (notBool_ v_15526);
      v_15531 <- getRegister cf;
      v_15536 <- eval (bit_or (bit_and v_15523 undef) (bit_and (notBool_ v_15523) (bit_or (bit_and v_15527 (eq (extract v_15520 0 1) (expression.bv_nat 1 1))) (bit_and v_15526 (eq v_15531 (expression.bv_nat 1 1))))));
      v_15539 <- eval (eq (extract v_15520 1 2) (expression.bv_nat 1 1));
      v_15541 <- getRegister sf;
      v_15548 <- getRegister zf;
      v_15553 <- eval (bit_and v_15527 undef);
      v_15554 <- getRegister af;
      v_15587 <- getRegister pf;
      v_15592 <- eval (eq v_15515 (expression.bv_nat 8 1));
      v_15597 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15592 (notBool_ (eq v_15536 v_15539))) (bit_and (notBool_ v_15592) (bit_or v_15553 (bit_and v_15526 (eq v_15597 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15527 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15520 8 9) (expression.bv_nat 1 1)) (eq (extract v_15520 7 8) (expression.bv_nat 1 1)))) (eq (extract v_15520 6 7) (expression.bv_nat 1 1)))) (eq (extract v_15520 5 6) (expression.bv_nat 1 1)))) (eq (extract v_15520 4 5) (expression.bv_nat 1 1)))) (eq (extract v_15520 3 4) (expression.bv_nat 1 1)))) (eq (extract v_15520 2 3) (expression.bv_nat 1 1)))) v_15539)) (bit_and v_15526 (eq v_15587 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15553 (bit_and v_15526 (eq v_15554 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15527 (eq v_15521 (expression.bv_nat 8 0))) (bit_and v_15526 (eq v_15548 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15527 v_15539) (bit_and v_15526 (eq v_15541 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15536 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2873 : Mem) => do
      v_18198 <- evaluateAddress v_2873;
      v_18199 <- load v_18198 1;
      v_18200 <- eval (concat (expression.bv_nat 1 0) v_18199);
      v_18203 <- eval (extract (shl v_18200 1) 0 (bitwidthMInt v_18200));
      v_18204 <- eval (extract v_18203 1 9);
      store v_18198 v_18204 1;
      v_18207 <- eval (eq (extract v_18203 0 1) (expression.bv_nat 1 1));
      v_18210 <- eval (eq (extract v_18203 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_18207 v_18210)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_18204);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18204);
      setRegister sf (mux v_18210 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18207 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2873 : Mem) => do
      v_18223 <- evaluateAddress v_2873;
      v_18224 <- load v_18223 1;
      v_18225 <- eval (concat (expression.bv_nat 1 0) v_18224);
      v_18228 <- eval (extract (shl v_18225 1) 0 (bitwidthMInt v_18225));
      v_18229 <- eval (extract v_18228 1 9);
      store v_18223 v_18229 1;
      v_18231 <- eval (extract v_18228 0 1);
      v_18232 <- eval (extract v_18228 1 2);
      setRegister of (mux (notBool_ (eq (eq v_18231 (expression.bv_nat 1 1)) (eq v_18232 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_18229);
      setRegister af undef;
      setRegister zf (zeroFlag v_18229);
      setRegister sf v_18232;
      setRegister cf v_18231;
      pure ()
    pat_end
