def vpmovsxwd1 : instruction :=
  definst "vpmovsxwd" $ do
    pattern fun (v_2663 : reg (bv 128)) (v_2664 : reg (bv 128)) => do
      v_5636 <- getRegister v_2663;
      setRegister (lhs.of_reg v_2664) (concat (mi 32 (svalueMInt (extract v_5636 64 80))) (concat (mi 32 (svalueMInt (extract v_5636 80 96))) (concat (mi 32 (svalueMInt (extract v_5636 96 112))) (mi 32 (svalueMInt (extract v_5636 112 128))))));
      pure ()
    pat_end;
    pattern fun (v_2672 : reg (bv 128)) (v_2673 : reg (bv 256)) => do
      v_5657 <- getRegister v_2672;
      setRegister (lhs.of_reg v_2673) (concat (mi 32 (svalueMInt (extract v_5657 0 16))) (concat (mi 32 (svalueMInt (extract v_5657 16 32))) (concat (mi 32 (svalueMInt (extract v_5657 32 48))) (concat (mi 32 (svalueMInt (extract v_5657 48 64))) (concat (mi 32 (svalueMInt (extract v_5657 64 80))) (concat (mi 32 (svalueMInt (extract v_5657 80 96))) (concat (mi 32 (svalueMInt (extract v_5657 96 112))) (mi 32 (svalueMInt (extract v_5657 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_2660 : Mem) (v_2659 : reg (bv 128)) => do
      v_12790 <- evaluateAddress v_2660;
      v_12791 <- load v_12790 8;
      setRegister (lhs.of_reg v_2659) (concat (mi 32 (svalueMInt (extract v_12791 0 16))) (concat (mi 32 (svalueMInt (extract v_12791 16 32))) (concat (mi 32 (svalueMInt (extract v_12791 32 48))) (mi 32 (svalueMInt (extract v_12791 48 64))))));
      pure ()
    pat_end;
    pattern fun (v_2668 : Mem) (v_2669 : reg (bv 256)) => do
      v_12808 <- evaluateAddress v_2668;
      v_12809 <- load v_12808 16;
      setRegister (lhs.of_reg v_2669) (concat (mi 32 (svalueMInt (extract v_12809 0 16))) (concat (mi 32 (svalueMInt (extract v_12809 16 32))) (concat (mi 32 (svalueMInt (extract v_12809 32 48))) (concat (mi 32 (svalueMInt (extract v_12809 48 64))) (concat (mi 32 (svalueMInt (extract v_12809 64 80))) (concat (mi 32 (svalueMInt (extract v_12809 80 96))) (concat (mi 32 (svalueMInt (extract v_12809 96 112))) (mi 32 (svalueMInt (extract v_12809 112 128))))))))));
      pure ()
    pat_end
