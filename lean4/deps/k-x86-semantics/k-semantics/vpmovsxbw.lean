def vpmovsxbw1 : instruction :=
  definst "vpmovsxbw" $ do
    pattern fun (v_2627 : reg (bv 128)) (v_2628 : reg (bv 128)) => do
      v_5496 <- getRegister v_2627;
      setRegister (lhs.of_reg v_2628) (concat (mi 16 (svalueMInt (extract v_5496 64 72))) (concat (mi 16 (svalueMInt (extract v_5496 72 80))) (concat (mi 16 (svalueMInt (extract v_5496 80 88))) (concat (mi 16 (svalueMInt (extract v_5496 88 96))) (concat (mi 16 (svalueMInt (extract v_5496 96 104))) (concat (mi 16 (svalueMInt (extract v_5496 104 112))) (concat (mi 16 (svalueMInt (extract v_5496 112 120))) (mi 16 (svalueMInt (extract v_5496 120 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_2636 : reg (bv 128)) (v_2637 : reg (bv 256)) => do
      v_5533 <- getRegister v_2636;
      setRegister (lhs.of_reg v_2637) (concat (mi 16 (svalueMInt (extract v_5533 0 8))) (concat (mi 16 (svalueMInt (extract v_5533 8 16))) (concat (mi 16 (svalueMInt (extract v_5533 16 24))) (concat (mi 16 (svalueMInt (extract v_5533 24 32))) (concat (mi 16 (svalueMInt (extract v_5533 32 40))) (concat (mi 16 (svalueMInt (extract v_5533 40 48))) (concat (mi 16 (svalueMInt (extract v_5533 48 56))) (concat (mi 16 (svalueMInt (extract v_5533 56 64))) (concat (mi 16 (svalueMInt (extract v_5533 64 72))) (concat (mi 16 (svalueMInt (extract v_5533 72 80))) (concat (mi 16 (svalueMInt (extract v_5533 80 88))) (concat (mi 16 (svalueMInt (extract v_5533 88 96))) (concat (mi 16 (svalueMInt (extract v_5533 96 104))) (concat (mi 16 (svalueMInt (extract v_5533 104 112))) (concat (mi 16 (svalueMInt (extract v_5533 112 120))) (mi 16 (svalueMInt (extract v_5533 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2624 : Mem) (v_2623 : reg (bv 128)) => do
      v_12662 <- evaluateAddress v_2624;
      v_12663 <- load v_12662 8;
      setRegister (lhs.of_reg v_2623) (concat (mi 16 (svalueMInt (extract v_12663 0 8))) (concat (mi 16 (svalueMInt (extract v_12663 8 16))) (concat (mi 16 (svalueMInt (extract v_12663 16 24))) (concat (mi 16 (svalueMInt (extract v_12663 24 32))) (concat (mi 16 (svalueMInt (extract v_12663 32 40))) (concat (mi 16 (svalueMInt (extract v_12663 40 48))) (concat (mi 16 (svalueMInt (extract v_12663 48 56))) (mi 16 (svalueMInt (extract v_12663 56 64))))))))));
      pure ()
    pat_end;
    pattern fun (v_2632 : Mem) (v_2633 : reg (bv 256)) => do
      v_12696 <- evaluateAddress v_2632;
      v_12697 <- load v_12696 16;
      setRegister (lhs.of_reg v_2633) (concat (mi 16 (svalueMInt (extract v_12697 0 8))) (concat (mi 16 (svalueMInt (extract v_12697 8 16))) (concat (mi 16 (svalueMInt (extract v_12697 16 24))) (concat (mi 16 (svalueMInt (extract v_12697 24 32))) (concat (mi 16 (svalueMInt (extract v_12697 32 40))) (concat (mi 16 (svalueMInt (extract v_12697 40 48))) (concat (mi 16 (svalueMInt (extract v_12697 48 56))) (concat (mi 16 (svalueMInt (extract v_12697 56 64))) (concat (mi 16 (svalueMInt (extract v_12697 64 72))) (concat (mi 16 (svalueMInt (extract v_12697 72 80))) (concat (mi 16 (svalueMInt (extract v_12697 80 88))) (concat (mi 16 (svalueMInt (extract v_12697 88 96))) (concat (mi 16 (svalueMInt (extract v_12697 96 104))) (concat (mi 16 (svalueMInt (extract v_12697 104 112))) (concat (mi 16 (svalueMInt (extract v_12697 112 120))) (mi 16 (svalueMInt (extract v_12697 120 128))))))))))))))))));
      pure ()
    pat_end
