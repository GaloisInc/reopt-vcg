def vpbroadcastq1 : instruction :=
  definst "vpbroadcastq" $ do
    pattern fun (v_2787 : reg (bv 128)) (v_2788 : reg (bv 128)) => do
      v_6969 <- getRegister v_2787;
      setRegister (lhs.of_reg v_2788) (concat (extract v_6969 64 128) (extract v_6969 64 128));
      pure ()
    pat_end;
    pattern fun (v_2797 : reg (bv 128)) (v_2795 : reg (bv 256)) => do
      v_6977 <- getRegister v_2797;
      setRegister (lhs.of_reg v_2795) (concat (concat (extract v_6977 64 128) (extract v_6977 64 128)) (concat (extract v_6977 64 128) (extract v_6977 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2782 : Mem) (v_2783 : reg (bv 128)) => do
      v_15602 <- evaluateAddress v_2782;
      v_15603 <- load v_15602 8;
      setRegister (lhs.of_reg v_2783) (concat v_15603 v_15603);
      pure ()
    pat_end;
    pattern fun (v_2791 : Mem) (v_2792 : reg (bv 256)) => do
      v_15606 <- evaluateAddress v_2791;
      v_15607 <- load v_15606 8;
      setRegister (lhs.of_reg v_2792) (concat (concat v_15607 v_15607) (concat v_15607 v_15607));
      pure ()
    pat_end
