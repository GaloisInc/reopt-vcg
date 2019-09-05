def shlb1 : instruction :=
  definst "shlb" $ do
    pattern fun cl (v_2797 : reg (bv 8)) => do
      v_4509 <- getRegister rcx;
      v_4511 <- eval (bv_and (extract v_4509 56 64) (expression.bv_nat 8 31));
      v_4512 <- eval (eq v_4511 (expression.bv_nat 8 0));
      v_4513 <- eval (notBool_ v_4512);
      v_4514 <- getRegister v_2797;
      v_4518 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4514) (concat (expression.bv_nat 1 0) v_4511)) 0 9);
      v_4519 <- eval (extract v_4518 1 9);
      v_4522 <- getRegister zf;
      v_4526 <- eval (isBitSet v_4518 1);
      v_4528 <- getRegister sf;
      v_4534 <- getRegister pf;
      v_4538 <- eval (eq v_4511 (expression.bv_nat 8 1));
      v_4539 <- eval (uge v_4511 (expression.bv_nat 8 8));
      v_4544 <- getRegister cf;
      v_4549 <- eval (bit_or (bit_and v_4539 undef) (bit_and (notBool_ v_4539) (bit_or (bit_and v_4513 (isBitSet v_4518 0)) (bit_and v_4512 (eq v_4544 (expression.bv_nat 1 1))))));
      v_4554 <- eval (bit_and v_4513 undef);
      v_4555 <- getRegister of;
      v_4561 <- getRegister af;
      setRegister (lhs.of_reg v_2797) v_4519;
      setRegister af (bit_or v_4554 (bit_and v_4512 (eq v_4561 (expression.bv_nat 1 1))));
      setRegister cf v_4549;
      setRegister of (bit_or (bit_and v_4538 (notBool_ (eq v_4549 v_4526))) (bit_and (notBool_ v_4538) (bit_or v_4554 (bit_and v_4512 (eq v_4555 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4513 (parityFlag v_4519)) (bit_and v_4512 (eq v_4534 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4513 v_4526) (bit_and v_4512 (eq v_4528 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4513 (eq v_4519 (expression.bv_nat 8 0))) (bit_and v_4512 (eq v_4522 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2800 : imm int) (v_2802 : reg (bv 8)) => do
      v_4573 <- eval (bv_and (handleImmediateWithSignExtend v_2800 8 8) (expression.bv_nat 8 31));
      v_4574 <- eval (eq v_4573 (expression.bv_nat 8 0));
      v_4575 <- eval (notBool_ v_4574);
      v_4576 <- getRegister v_2802;
      v_4580 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4576) (concat (expression.bv_nat 1 0) v_4573)) 0 9);
      v_4581 <- eval (extract v_4580 1 9);
      v_4584 <- getRegister zf;
      v_4588 <- eval (isBitSet v_4580 1);
      v_4590 <- getRegister sf;
      v_4596 <- getRegister pf;
      v_4600 <- eval (eq v_4573 (expression.bv_nat 8 1));
      v_4601 <- eval (uge v_4573 (expression.bv_nat 8 8));
      v_4606 <- getRegister cf;
      v_4611 <- eval (bit_or (bit_and v_4601 undef) (bit_and (notBool_ v_4601) (bit_or (bit_and v_4575 (isBitSet v_4580 0)) (bit_and v_4574 (eq v_4606 (expression.bv_nat 1 1))))));
      v_4616 <- eval (bit_and v_4575 undef);
      v_4617 <- getRegister of;
      v_4623 <- getRegister af;
      setRegister (lhs.of_reg v_2802) v_4581;
      setRegister af (bit_or v_4616 (bit_and v_4574 (eq v_4623 (expression.bv_nat 1 1))));
      setRegister cf v_4611;
      setRegister of (bit_or (bit_and v_4600 (notBool_ (eq v_4611 v_4588))) (bit_and (notBool_ v_4600) (bit_or v_4616 (bit_and v_4574 (eq v_4617 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4575 (parityFlag v_4581)) (bit_and v_4574 (eq v_4596 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4575 v_4588) (bit_and v_4574 (eq v_4590 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4575 (eq v_4581 (expression.bv_nat 8 0))) (bit_and v_4574 (eq v_4584 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun cl (v_2773 : Mem) => do
      v_9432 <- evaluateAddress v_2773;
      v_9433 <- load v_9432 1;
      v_9435 <- getRegister rcx;
      v_9437 <- eval (bv_and (extract v_9435 56 64) (expression.bv_nat 8 31));
      v_9440 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9433) (concat (expression.bv_nat 1 0) v_9437)) 0 9);
      v_9441 <- eval (extract v_9440 1 9);
      store v_9432 v_9441 1;
      v_9443 <- eval (eq v_9437 (expression.bv_nat 8 0));
      v_9444 <- eval (notBool_ v_9443);
      v_9447 <- getRegister zf;
      v_9451 <- eval (isBitSet v_9440 1);
      v_9453 <- getRegister sf;
      v_9459 <- getRegister pf;
      v_9463 <- eval (eq v_9437 (expression.bv_nat 8 1));
      v_9464 <- eval (uge v_9437 (expression.bv_nat 8 8));
      v_9469 <- getRegister cf;
      v_9474 <- eval (bit_or (bit_and v_9464 undef) (bit_and (notBool_ v_9464) (bit_or (bit_and v_9444 (isBitSet v_9440 0)) (bit_and v_9443 (eq v_9469 (expression.bv_nat 1 1))))));
      v_9479 <- eval (bit_and v_9444 undef);
      v_9480 <- getRegister of;
      v_9486 <- getRegister af;
      setRegister af (bit_or v_9479 (bit_and v_9443 (eq v_9486 (expression.bv_nat 1 1))));
      setRegister cf v_9474;
      setRegister of (bit_or (bit_and v_9463 (notBool_ (eq v_9474 v_9451))) (bit_and (notBool_ v_9463) (bit_or v_9479 (bit_and v_9443 (eq v_9480 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9444 (parityFlag v_9441)) (bit_and v_9443 (eq v_9459 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9444 v_9451) (bit_and v_9443 (eq v_9453 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9444 (eq v_9441 (expression.bv_nat 8 0))) (bit_and v_9443 (eq v_9447 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2777 : imm int) (v_2776 : Mem) => do
      v_9496 <- evaluateAddress v_2776;
      v_9497 <- load v_9496 1;
      v_9500 <- eval (bv_and (handleImmediateWithSignExtend v_2777 8 8) (expression.bv_nat 8 31));
      v_9503 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9497) (concat (expression.bv_nat 1 0) v_9500)) 0 9);
      v_9504 <- eval (extract v_9503 1 9);
      store v_9496 v_9504 1;
      v_9506 <- eval (eq v_9500 (expression.bv_nat 8 0));
      v_9507 <- eval (notBool_ v_9506);
      v_9510 <- getRegister zf;
      v_9514 <- eval (isBitSet v_9503 1);
      v_9516 <- getRegister sf;
      v_9522 <- getRegister pf;
      v_9526 <- eval (eq v_9500 (expression.bv_nat 8 1));
      v_9527 <- eval (uge v_9500 (expression.bv_nat 8 8));
      v_9532 <- getRegister cf;
      v_9537 <- eval (bit_or (bit_and v_9527 undef) (bit_and (notBool_ v_9527) (bit_or (bit_and v_9507 (isBitSet v_9503 0)) (bit_and v_9506 (eq v_9532 (expression.bv_nat 1 1))))));
      v_9542 <- eval (bit_and v_9507 undef);
      v_9543 <- getRegister of;
      v_9549 <- getRegister af;
      setRegister af (bit_or v_9542 (bit_and v_9506 (eq v_9549 (expression.bv_nat 1 1))));
      setRegister cf v_9537;
      setRegister of (bit_or (bit_and v_9526 (notBool_ (eq v_9537 v_9514))) (bit_and (notBool_ v_9526) (bit_or v_9542 (bit_and v_9506 (eq v_9543 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9507 (parityFlag v_9504)) (bit_and v_9506 (eq v_9522 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9507 v_9514) (bit_and v_9506 (eq v_9516 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9507 (eq v_9504 (expression.bv_nat 8 0))) (bit_and v_9506 (eq v_9510 (expression.bv_nat 1 1))));
      pure ()
    pat_end
