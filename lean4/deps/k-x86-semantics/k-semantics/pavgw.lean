def pavgw1 : instruction :=
  definst "pavgw" $ do
    pattern fun (v_3233 : reg (bv 128)) (v_3234 : reg (bv 128)) => do
      v_6560 <- getRegister v_3234;
      v_6563 <- getRegister v_3233;
      setRegister (lhs.of_reg v_3234) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 0 16)) (concat (expression.bv_nat 1 0) (extract v_6563 0 16))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 16 32)) (concat (expression.bv_nat 1 0) (extract v_6563 16 32))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 32 48)) (concat (expression.bv_nat 1 0) (extract v_6563 32 48))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 48 64)) (concat (expression.bv_nat 1 0) (extract v_6563 48 64))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 64 80)) (concat (expression.bv_nat 1 0) (extract v_6563 64 80))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 80 96)) (concat (expression.bv_nat 1 0) (extract v_6563 80 96))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 96 112)) (concat (expression.bv_nat 1 0) (extract v_6563 96 112))) (expression.bv_nat 17 1)) 1) 1 17) (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_6560 112 128)) (concat (expression.bv_nat 1 0) (extract v_6563 112 128))) (expression.bv_nat 17 1)) 1) 1 17))))))));
      pure ()
    pat_end;
    pattern fun (v_3229 : Mem) (v_3230 : reg (bv 128)) => do
      v_10607 <- getRegister v_3230;
      v_10610 <- evaluateAddress v_3229;
      v_10611 <- load v_10610 16;
      setRegister (lhs.of_reg v_3230) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 0 16)) (concat (expression.bv_nat 1 0) (extract v_10611 0 16))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 16 32)) (concat (expression.bv_nat 1 0) (extract v_10611 16 32))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 32 48)) (concat (expression.bv_nat 1 0) (extract v_10611 32 48))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 48 64)) (concat (expression.bv_nat 1 0) (extract v_10611 48 64))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 64 80)) (concat (expression.bv_nat 1 0) (extract v_10611 64 80))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 80 96)) (concat (expression.bv_nat 1 0) (extract v_10611 80 96))) (expression.bv_nat 17 1)) 1) 1 17) (concat (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 96 112)) (concat (expression.bv_nat 1 0) (extract v_10611 96 112))) (expression.bv_nat 17 1)) 1) 1 17) (extract (lshr (add (add (concat (expression.bv_nat 1 0) (extract v_10607 112 128)) (concat (expression.bv_nat 1 0) (extract v_10611 112 128))) (expression.bv_nat 17 1)) 1) 1 17))))))));
      pure ()
    pat_end
