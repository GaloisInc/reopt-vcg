def vpbroadcastd1 : instruction :=
  definst "vpbroadcastd" $ do
    pattern fun (v_2795 : reg (bv 128)) (v_2796 : reg (bv 128)) => do
      v_6975 <- getRegister v_2795;
      v_6976 <- eval (extract v_6975 96 128);
      setRegister (lhs.of_reg v_2796) (concat (concat (concat v_6976 v_6976) v_6976) v_6976);
      pure ()
    pat_end;
    pattern fun (v_2805 : reg (bv 128)) (v_2804 : reg (bv 256)) => do
      v_6985 <- getRegister v_2805;
      v_6986 <- eval (extract v_6985 96 128);
      setRegister (lhs.of_reg v_2804) (concat (concat (concat (concat v_6986 v_6986) v_6986) v_6986) (concat (concat (concat v_6986 v_6986) v_6986) v_6986));
      pure ()
    pat_end;
    pattern fun (v_2791 : Mem) (v_2792 : reg (bv 128)) => do
      v_15616 <- evaluateAddress v_2791;
      v_15617 <- load v_15616 4;
      setRegister (lhs.of_reg v_2792) (concat (concat (concat v_15617 v_15617) v_15617) v_15617);
      pure ()
    pat_end;
    pattern fun (v_2800 : Mem) (v_2801 : reg (bv 256)) => do
      v_15622 <- evaluateAddress v_2800;
      v_15623 <- load v_15622 4;
      setRegister (lhs.of_reg v_2801) (concat (concat (concat (concat v_15623 v_15623) v_15623) v_15623) (concat (concat (concat v_15623 v_15623) v_15623) v_15623));
      pure ()
    pat_end
