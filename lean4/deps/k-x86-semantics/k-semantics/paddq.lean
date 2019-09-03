def paddq1 : instruction :=
  definst "paddq" $ do
    pattern fun (v_3141 : reg (bv 128)) (v_3142 : reg (bv 128)) => do
      v_5797 <- getRegister v_3142;
      v_5799 <- getRegister v_3141;
      setRegister (lhs.of_reg v_3142) (concat (add (extract v_5797 0 64) (extract v_5799 0 64)) (add (extract v_5797 64 128) (extract v_5799 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3137 : Mem) (v_3138 : reg (bv 128)) => do
      v_9875 <- getRegister v_3138;
      v_9877 <- evaluateAddress v_3137;
      v_9878 <- load v_9877 16;
      setRegister (lhs.of_reg v_3138) (concat (add (extract v_9875 0 64) (extract v_9878 0 64)) (add (extract v_9875 64 128) (extract v_9878 64 128)));
      pure ()
    pat_end
