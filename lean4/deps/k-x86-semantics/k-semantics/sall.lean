def sall1 : instruction :=
  definst "sall" $ do
    pattern fun cl (v_2924 : reg (bv 32)) => do
      v_6329 <- getRegister rcx;
      v_6331 <- eval (bv_and (extract v_6329 56 64) (expression.bv_nat 8 31));
      v_6332 <- eval (uge v_6331 (expression.bv_nat 8 32));
      v_6335 <- eval (eq v_6331 (expression.bv_nat 8 0));
      v_6336 <- eval (notBool_ v_6335);
      v_6337 <- getRegister v_2924;
      v_6338 <- eval (concat (expression.bv_nat 1 0) v_6337);
      v_6343 <- eval (extract (shl v_6338 (uvalueMInt (concat (expression.bv_nat 25 0) v_6331))) 0 (bitwidthMInt v_6338));
      v_6347 <- getRegister cf;
      v_6352 <- eval (bit_or (bit_and v_6332 undef) (bit_and (notBool_ v_6332) (bit_or (bit_and v_6336 (eq (extract v_6343 0 1) (expression.bv_nat 1 1))) (bit_and v_6335 (eq v_6347 (expression.bv_nat 1 1))))));
      v_6355 <- eval (eq (extract v_6343 1 2) (expression.bv_nat 1 1));
      v_6357 <- getRegister sf;
      v_6362 <- eval (bit_and v_6336 undef);
      v_6363 <- getRegister af;
      v_6368 <- eval (extract v_6343 1 33);
      v_6371 <- getRegister zf;
      v_6406 <- getRegister pf;
      v_6411 <- eval (eq v_6331 (expression.bv_nat 8 1));
      v_6416 <- getRegister of;
      setRegister (lhs.of_reg v_2924) v_6368;
      setRegister of (mux (bit_or (bit_and v_6411 (notBool_ (eq v_6352 v_6355))) (bit_and (notBool_ v_6411) (bit_or v_6362 (bit_and v_6335 (eq v_6416 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6336 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6343 32 33) (expression.bv_nat 1 1)) (eq (extract v_6343 31 32) (expression.bv_nat 1 1)))) (eq (extract v_6343 30 31) (expression.bv_nat 1 1)))) (eq (extract v_6343 29 30) (expression.bv_nat 1 1)))) (eq (extract v_6343 28 29) (expression.bv_nat 1 1)))) (eq (extract v_6343 27 28) (expression.bv_nat 1 1)))) (eq (extract v_6343 26 27) (expression.bv_nat 1 1)))) (eq (extract v_6343 25 26) (expression.bv_nat 1 1)))) (bit_and v_6335 (eq v_6406 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6336 (eq v_6368 (expression.bv_nat 32 0))) (bit_and v_6335 (eq v_6371 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6362 (bit_and v_6335 (eq v_6363 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6336 v_6355) (bit_and v_6335 (eq v_6357 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6352 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2926 : imm int) (v_2929 : reg (bv 32)) => do
      v_6431 <- eval (bv_and (handleImmediateWithSignExtend v_2926 8 8) (expression.bv_nat 8 31));
      v_6432 <- eval (uge v_6431 (expression.bv_nat 8 32));
      v_6435 <- eval (eq v_6431 (expression.bv_nat 8 0));
      v_6436 <- eval (notBool_ v_6435);
      v_6437 <- getRegister v_2929;
      v_6438 <- eval (concat (expression.bv_nat 1 0) v_6437);
      v_6443 <- eval (extract (shl v_6438 (uvalueMInt (concat (expression.bv_nat 25 0) v_6431))) 0 (bitwidthMInt v_6438));
      v_6447 <- getRegister cf;
      v_6452 <- eval (bit_or (bit_and v_6432 undef) (bit_and (notBool_ v_6432) (bit_or (bit_and v_6436 (eq (extract v_6443 0 1) (expression.bv_nat 1 1))) (bit_and v_6435 (eq v_6447 (expression.bv_nat 1 1))))));
      v_6455 <- eval (eq (extract v_6443 1 2) (expression.bv_nat 1 1));
      v_6457 <- getRegister sf;
      v_6462 <- eval (bit_and v_6436 undef);
      v_6463 <- getRegister af;
      v_6468 <- eval (extract v_6443 1 33);
      v_6471 <- getRegister zf;
      v_6506 <- getRegister pf;
      v_6511 <- eval (eq v_6431 (expression.bv_nat 8 1));
      v_6516 <- getRegister of;
      setRegister (lhs.of_reg v_2929) v_6468;
      setRegister of (mux (bit_or (bit_and v_6511 (notBool_ (eq v_6452 v_6455))) (bit_and (notBool_ v_6511) (bit_or v_6462 (bit_and v_6435 (eq v_6516 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6436 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6443 32 33) (expression.bv_nat 1 1)) (eq (extract v_6443 31 32) (expression.bv_nat 1 1)))) (eq (extract v_6443 30 31) (expression.bv_nat 1 1)))) (eq (extract v_6443 29 30) (expression.bv_nat 1 1)))) (eq (extract v_6443 28 29) (expression.bv_nat 1 1)))) (eq (extract v_6443 27 28) (expression.bv_nat 1 1)))) (eq (extract v_6443 26 27) (expression.bv_nat 1 1)))) (eq (extract v_6443 25 26) (expression.bv_nat 1 1)))) (bit_and v_6435 (eq v_6506 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6436 (eq v_6468 (expression.bv_nat 32 0))) (bit_and v_6435 (eq v_6471 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6462 (bit_and v_6435 (eq v_6463 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6436 v_6455) (bit_and v_6435 (eq v_6457 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6452 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2936 : reg (bv 32)) => do
      v_6532 <- getRegister v_2936;
      v_6533 <- eval (concat (expression.bv_nat 1 0) v_6532);
      v_6536 <- eval (extract (shl v_6533 1) 0 (bitwidthMInt v_6533));
      v_6537 <- eval (extract v_6536 0 1);
      v_6538 <- eval (extract v_6536 1 2);
      v_6539 <- eval (extract v_6536 1 33);
      setRegister (lhs.of_reg v_2936) v_6539;
      setRegister of (mux (notBool_ (eq (eq v_6537 (expression.bv_nat 1 1)) (eq v_6538 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_6536 25 33));
      setRegister zf (zeroFlag v_6539);
      setRegister af undef;
      setRegister sf v_6538;
      setRegister cf v_6537;
      pure ()
    pat_end;
    pattern fun (v_2933 : reg (bv 32)) => do
      v_9515 <- getRegister v_2933;
      v_9516 <- eval (concat (expression.bv_nat 1 0) v_9515);
      v_9519 <- eval (extract (shl v_9516 1) 0 (bitwidthMInt v_9516));
      v_9521 <- eval (eq (extract v_9519 0 1) (expression.bv_nat 1 1));
      v_9524 <- eval (eq (extract v_9519 1 2) (expression.bv_nat 1 1));
      v_9526 <- eval (extract v_9519 1 33);
      setRegister (lhs.of_reg v_2933) v_9526;
      setRegister of (mux (notBool_ (eq v_9521 v_9524)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9519 25 33));
      setRegister zf (zeroFlag v_9526);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux v_9524 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9521 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2933 : reg (bv 32)) => do
      v_9540 <- getRegister v_2933;
      v_9541 <- eval (concat (expression.bv_nat 1 0) v_9540);
      v_9544 <- eval (extract (shl v_9541 1) 0 (bitwidthMInt v_9541));
      v_9545 <- eval (extract v_9544 0 1);
      v_9546 <- eval (extract v_9544 1 2);
      v_9547 <- eval (extract v_9544 1 33);
      setRegister (lhs.of_reg v_2933) v_9547;
      setRegister of (mux (notBool_ (eq (eq v_9545 (expression.bv_nat 1 1)) (eq v_9546 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9544 25 33));
      setRegister zf (zeroFlag v_9547);
      setRegister af undef;
      setRegister sf v_9546;
      setRegister cf v_9545;
      pure ()
    pat_end;
    pattern fun cl (v_2909 : Mem) => do
      v_15708 <- evaluateAddress v_2909;
      v_15709 <- load v_15708 4;
      v_15710 <- eval (concat (expression.bv_nat 1 0) v_15709);
      v_15711 <- getRegister rcx;
      v_15713 <- eval (bv_and (extract v_15711 56 64) (expression.bv_nat 8 31));
      v_15718 <- eval (extract (shl v_15710 (uvalueMInt (concat (expression.bv_nat 25 0) v_15713))) 0 (bitwidthMInt v_15710));
      v_15719 <- eval (extract v_15718 1 33);
      store v_15708 v_15719 4;
      v_15721 <- eval (uge v_15713 (expression.bv_nat 8 32));
      v_15724 <- eval (eq v_15713 (expression.bv_nat 8 0));
      v_15725 <- eval (notBool_ v_15724);
      v_15729 <- getRegister cf;
      v_15734 <- eval (bit_or (bit_and v_15721 undef) (bit_and (notBool_ v_15721) (bit_or (bit_and v_15725 (eq (extract v_15718 0 1) (expression.bv_nat 1 1))) (bit_and v_15724 (eq v_15729 (expression.bv_nat 1 1))))));
      v_15737 <- eval (eq (extract v_15718 1 2) (expression.bv_nat 1 1));
      v_15739 <- getRegister sf;
      v_15746 <- getRegister zf;
      v_15751 <- eval (bit_and v_15725 undef);
      v_15752 <- getRegister af;
      v_15787 <- getRegister pf;
      v_15792 <- eval (eq v_15713 (expression.bv_nat 8 1));
      v_15797 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15792 (notBool_ (eq v_15734 v_15737))) (bit_and (notBool_ v_15792) (bit_or v_15751 (bit_and v_15724 (eq v_15797 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15725 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15718 32 33) (expression.bv_nat 1 1)) (eq (extract v_15718 31 32) (expression.bv_nat 1 1)))) (eq (extract v_15718 30 31) (expression.bv_nat 1 1)))) (eq (extract v_15718 29 30) (expression.bv_nat 1 1)))) (eq (extract v_15718 28 29) (expression.bv_nat 1 1)))) (eq (extract v_15718 27 28) (expression.bv_nat 1 1)))) (eq (extract v_15718 26 27) (expression.bv_nat 1 1)))) (eq (extract v_15718 25 26) (expression.bv_nat 1 1)))) (bit_and v_15724 (eq v_15787 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15751 (bit_and v_15724 (eq v_15752 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15725 (eq v_15719 (expression.bv_nat 32 0))) (bit_and v_15724 (eq v_15746 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15725 v_15737) (bit_and v_15724 (eq v_15739 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15734 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2912 : imm int) (v_2913 : Mem) => do
      v_15810 <- evaluateAddress v_2913;
      v_15811 <- load v_15810 4;
      v_15812 <- eval (concat (expression.bv_nat 1 0) v_15811);
      v_15814 <- eval (bv_and (handleImmediateWithSignExtend v_2912 8 8) (expression.bv_nat 8 31));
      v_15819 <- eval (extract (shl v_15812 (uvalueMInt (concat (expression.bv_nat 25 0) v_15814))) 0 (bitwidthMInt v_15812));
      v_15820 <- eval (extract v_15819 1 33);
      store v_15810 v_15820 4;
      v_15822 <- eval (uge v_15814 (expression.bv_nat 8 32));
      v_15825 <- eval (eq v_15814 (expression.bv_nat 8 0));
      v_15826 <- eval (notBool_ v_15825);
      v_15830 <- getRegister cf;
      v_15835 <- eval (bit_or (bit_and v_15822 undef) (bit_and (notBool_ v_15822) (bit_or (bit_and v_15826 (eq (extract v_15819 0 1) (expression.bv_nat 1 1))) (bit_and v_15825 (eq v_15830 (expression.bv_nat 1 1))))));
      v_15838 <- eval (eq (extract v_15819 1 2) (expression.bv_nat 1 1));
      v_15840 <- getRegister sf;
      v_15847 <- getRegister zf;
      v_15852 <- eval (bit_and v_15826 undef);
      v_15853 <- getRegister af;
      v_15888 <- getRegister pf;
      v_15893 <- eval (eq v_15814 (expression.bv_nat 8 1));
      v_15898 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15893 (notBool_ (eq v_15835 v_15838))) (bit_and (notBool_ v_15893) (bit_or v_15852 (bit_and v_15825 (eq v_15898 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15826 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15819 32 33) (expression.bv_nat 1 1)) (eq (extract v_15819 31 32) (expression.bv_nat 1 1)))) (eq (extract v_15819 30 31) (expression.bv_nat 1 1)))) (eq (extract v_15819 29 30) (expression.bv_nat 1 1)))) (eq (extract v_15819 28 29) (expression.bv_nat 1 1)))) (eq (extract v_15819 27 28) (expression.bv_nat 1 1)))) (eq (extract v_15819 26 27) (expression.bv_nat 1 1)))) (eq (extract v_15819 25 26) (expression.bv_nat 1 1)))) (bit_and v_15825 (eq v_15888 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15852 (bit_and v_15825 (eq v_15853 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15826 (eq v_15820 (expression.bv_nat 32 0))) (bit_and v_15825 (eq v_15847 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15826 v_15838) (bit_and v_15825 (eq v_15840 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15835 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2918 : Mem) => do
      v_18246 <- evaluateAddress v_2918;
      v_18247 <- load v_18246 4;
      v_18248 <- eval (concat (expression.bv_nat 1 0) v_18247);
      v_18251 <- eval (extract (shl v_18248 1) 0 (bitwidthMInt v_18248));
      v_18252 <- eval (extract v_18251 1 33);
      store v_18246 v_18252 4;
      v_18255 <- eval (eq (extract v_18251 0 1) (expression.bv_nat 1 1));
      v_18258 <- eval (eq (extract v_18251 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_18255 v_18258)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18251 25 33));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18252);
      setRegister sf (mux v_18258 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18255 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2918 : Mem) => do
      v_18272 <- evaluateAddress v_2918;
      v_18273 <- load v_18272 4;
      v_18274 <- eval (concat (expression.bv_nat 1 0) v_18273);
      v_18277 <- eval (extract (shl v_18274 1) 0 (bitwidthMInt v_18274));
      v_18278 <- eval (extract v_18277 1 33);
      store v_18272 v_18278 4;
      v_18280 <- eval (extract v_18277 0 1);
      v_18281 <- eval (extract v_18277 1 2);
      setRegister of (mux (notBool_ (eq (eq v_18280 (expression.bv_nat 1 1)) (eq v_18281 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18277 25 33));
      setRegister af undef;
      setRegister zf (zeroFlag v_18278);
      setRegister sf v_18281;
      setRegister cf v_18280;
      pure ()
    pat_end
