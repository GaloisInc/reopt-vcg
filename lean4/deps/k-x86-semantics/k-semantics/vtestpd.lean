def vtestpd1 : instruction :=
  definst "vtestpd" $ do
    pattern fun (v_2426 : reg (bv 128)) (v_2427 : reg (bv 128)) => do
      v_3388 <- getRegister v_2427;
      v_3389 <- eval (extract v_3388 64 65);
      v_3393 <- getRegister v_2426;
      v_3394 <- eval (extract v_3393 64 65);
      v_3397 <- eval (extract v_3388 0 1);
      v_3401 <- eval (extract v_3393 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (eq (bv_and v_3389 v_3394) (expression.bv_nat 1 0)) (eq (bv_and v_3397 v_3401) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (eq (bv_and (bv_xor v_3389 (mi (bitwidthMInt v_3389) -1)) v_3394) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_3397 (mi (bitwidthMInt v_3397) -1)) v_3401) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2436 : reg (bv 256)) (v_2437 : reg (bv 256)) => do
      v_3422 <- getRegister v_2437;
      v_3423 <- eval (extract v_3422 192 193);
      v_3427 <- getRegister v_2436;
      v_3428 <- eval (extract v_3427 192 193);
      v_3431 <- eval (extract v_3422 128 129);
      v_3435 <- eval (extract v_3427 128 129);
      v_3439 <- eval (extract v_3422 64 65);
      v_3443 <- eval (extract v_3427 64 65);
      v_3447 <- eval (extract v_3422 0 1);
      v_3451 <- eval (extract v_3427 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (bit_and (bit_and (eq (bv_and v_3423 v_3428) (expression.bv_nat 1 0)) (eq (bv_and v_3431 v_3435) (expression.bv_nat 1 0))) (eq (bv_and v_3439 v_3443) (expression.bv_nat 1 0))) (eq (bv_and v_3447 v_3451) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_3423 (mi (bitwidthMInt v_3423) -1)) v_3428) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_3431 (mi (bitwidthMInt v_3431) -1)) v_3435) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3439 (mi (bitwidthMInt v_3439) -1)) v_3443) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3447 (mi (bitwidthMInt v_3447) -1)) v_3451) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2422 : Mem) (v_2423 : reg (bv 128)) => do
      v_6660 <- getRegister v_2423;
      v_6661 <- eval (extract v_6660 64 65);
      v_6665 <- evaluateAddress v_2422;
      v_6666 <- load v_6665 16;
      v_6667 <- eval (extract v_6666 64 65);
      v_6670 <- eval (extract v_6660 0 1);
      v_6674 <- eval (extract v_6666 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (eq (bv_and v_6661 v_6667) (expression.bv_nat 1 0)) (eq (bv_and v_6670 v_6674) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (eq (bv_and (bv_xor v_6661 (mi (bitwidthMInt v_6661) -1)) v_6667) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_6670 (mi (bitwidthMInt v_6670) -1)) v_6674) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2431 : Mem) (v_2432 : reg (bv 256)) => do
      v_6691 <- getRegister v_2432;
      v_6692 <- eval (extract v_6691 192 193);
      v_6696 <- evaluateAddress v_2431;
      v_6697 <- load v_6696 32;
      v_6698 <- eval (extract v_6697 192 193);
      v_6701 <- eval (extract v_6691 128 129);
      v_6705 <- eval (extract v_6697 128 129);
      v_6709 <- eval (extract v_6691 64 65);
      v_6713 <- eval (extract v_6697 64 65);
      v_6717 <- eval (extract v_6691 0 1);
      v_6721 <- eval (extract v_6697 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (bit_and (bit_and (eq (bv_and v_6692 v_6698) (expression.bv_nat 1 0)) (eq (bv_and v_6701 v_6705) (expression.bv_nat 1 0))) (eq (bv_and v_6709 v_6713) (expression.bv_nat 1 0))) (eq (bv_and v_6717 v_6721) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_6692 (mi (bitwidthMInt v_6692) -1)) v_6698) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_6701 (mi (bitwidthMInt v_6701) -1)) v_6705) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6709 (mi (bitwidthMInt v_6709) -1)) v_6713) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6717 (mi (bitwidthMInt v_6717) -1)) v_6721) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
