library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package macle_runtime is
  type    unit is (unit_value);
  alias   bool is std_logic;
  subtype int  is signed(30 downto 0);
  subtype value  is unsigned(31 downto 0);
  alias   header is value;

  constant macle_true : bool := '1'; 
  constant macle_false : bool := '0';
  constant macle_unit : unit := unit_value;
  constant zero : value := (others => '0');
  constant none : value := zero;

  constant empty_array : value := zero;
  constant empty_list : value := zero;

  -- Macle core

  function macle_int(i:integer) return int;

  function macle_exception(i:integer) return value;

  function macle_not(v1 : bool) return bool;
  function macle_neg(v1 : int) return int;

  function macle_add(v1 : int; v2 : int) return int;
  function macle_sub(v1 : int; v2 : int) return int;
  function macle_mul(v1 : int; v2 : int) return int;
  function macle_div(v1 : int; v2 : int) return int;
  function macle_mod(v1 : int; v2 : int) return int;
  function macle_lt(v1 : int; v2 : int) return bool;
  function macle_le(v1 : int; v2 : int) return bool;
  function macle_gt(v1 : int; v2 : int) return bool;
  function macle_ge(v1 : int; v2 : int) return bool;
  
  function macle_eq(v1 : unit; v2 : unit) return bool;
  function macle_eq(v1 : int; v2 : int) return bool;
  function macle_eq(v1 : bool; v2 : bool) return bool;
  function macle_eq(v1 : value; v2 : value) return bool;
  
  function macle_neq(v1 : unit; v2 : unit) return bool;
  function macle_neq(v1 : int; v2 : int) return bool;
  function macle_neq(v1 : bool; v2 : bool) return bool;
  function macle_neq(v1 : value; v2 : value) return bool;

  function macle_or(v1 : bool; v2 : bool) return bool;
  function macle_and(v1 : bool; v2 : bool) return bool;
  
  function macle_if(v1 : bool; v2 : bool ; v3 : bool) return bool;
  function macle_if(v1 : bool; v2 : int ; v3 : int) return int;
  function macle_if(v1 : bool; v2 : unit ; v3 : unit) return unit;
  function macle_if(v1 : bool; v2 : value ; v3 : value) return value;

  -- interaction with the OCaml runtime
  function magic_value(data : value) return value;
  function magic_value(data : value) return int;
  function magic_value(data : value) return bool;
  function magic_value(data : value) return unit;

  function magic_value(data : unit) return value;
  function magic_value(data : int) return value;
  function magic_value(data : bool) return value;
  --function Bool_val(v : value) return bool;
  --function Int_val(v : value) return int;
  --function Val_int(n : int) return value;
  --function Val_bool(b : bool) return value;

  function ram_field(ram_start : value; addr : value; field:int) return value;
  function size_hd(hd : header) return int;   
  function tag_hd(hd : header) return int;
  function as_immediate(v : value) return int;
  function is_immediate(x : value) return bool;

end;

package body macle_runtime is

   function bool_of_boolean(b:boolean) return bool is begin 
      if b then 
        return macle_true;
      else 
        return macle_false; 
      end if;
    end;

  function macle_int(i:integer) return int is begin 
      return to_signed(i,31); 
    end;

  function macle_exception(i:integer) return value is begin
    return to_unsigned(i,32); 
  end;

  function macle_not(v1 : bool) return bool is
  begin 
    if v1 = '1' then 
      return macle_false; 
    else 
      return macle_true;
    end if;
  end;
  function macle_neg(v1 : int) return int is
  begin 
    return 0 - v1;
  end;

  function macle_add(v1 : int; v2 : int) return int is
    begin 
      return v1 + v2;
    end;
  
  function macle_sub(v1 : int; v2 : int) return int is
    begin
      return v1 - v2; 
    end;
  
  function macle_mul(v1 : int; v2 : int) return int is
    begin 
      return resize(v1 * v2,31); 
    end;

  function macle_div(v1 : int; v2 : int) return int is
    begin 
      return v1 / v2;
    end;

  function macle_mod(v1 : int; v2 : int) return int is
    begin 
      return v1 mod v2;
    end;

  function macle_lt(v1 : int; v2 : int) return bool is
    begin 
      return bool_of_boolean(v1 < v2); 
    end;

  function macle_le(v1 : int; v2 : int) return bool is
    begin
      return bool_of_boolean(v1 <= v2); 
    end;

  function macle_gt(v1 : int; v2 : int) return bool is
    begin 
      return bool_of_boolean(v1 > v2); 
    end;

  function macle_ge(v1 : int; v2 : int) return bool is
    begin 
      return bool_of_boolean(v1 >= v2); 
    end;

  function macle_eq(v1 : int; v2 : int) return bool is
    begin 
      return bool_of_boolean(v1 = v2); 
    end;

  function macle_eq(v1 : unit; v2 : unit) return bool is
    begin 
      return bool_of_boolean(v1 = v2); 
    end;

  function macle_eq(v1 : bool; v2 : bool) return bool is
    begin 
      return bool_of_boolean(v1 = v2);
    end;

  function macle_eq(v1 : value; v2 : value) return bool is
    begin 
      return bool_of_boolean(v1 = v2); 
    end;

  function macle_neq(v1 : int; v2 : int) return bool is
    begin 
      return macle_not(macle_eq(v1, v2)); 
    end;

  function macle_neq(v1 : bool; v2 : bool) return bool is
    begin 
      return macle_not(macle_eq(v1, v2)); 
    end;

  function macle_neq(v1 : unit; v2 : unit) return bool is
    begin 
      return macle_not(macle_eq(v1, v2)); 
    end;

  function macle_neq(v1 : value; v2 : value) return bool is
  begin 
    return macle_not(macle_eq(v1, v2)); 
  end;

  function macle_or(v1 : bool; v2 : bool) return bool is
    begin 
      return v1 or v2; 
    end;

  function macle_and(v1 : bool; v2 : bool) return bool is
    begin 
      return v1 and v2; 
    end;
  
  function macle_if(v1 : bool; v2 : bool ; v3 : bool) return bool is
    begin
      if v1 = macle_true then
        return v2;
      else
        return v3;
      end if;
    end;
  
  function macle_if(v1 : bool; v2 : unit ; v3 : unit) return unit is
    begin
        return unit_value;
    end;
  
  function macle_if(v1 : bool; v2 : int ; v3 : int) return int is
    begin
      if v1 = macle_true then
        return v2;
      else
        return v3;
      end if;
    end;
  
  function macle_if(v1 : bool; v2 : value ; v3 : value) return value is
    begin
      if v1 = macle_true then
        return v2;
      else
        return v3;
      end if;
    end;

  -- interaction with the OCaml runtime

  function magic_value(data : value) return value is
    begin
      return unsigned(data);
    end;
  function magic_value(data : value) return int is
    begin
      return signed(data(31 downto 1));
    end;
  function magic_value(data : value) return bool is
    begin
      return data(0);
    end;
  function magic_value(data : value) return unit is
    begin
      return unit_value;
    end;

  function magic_value(data : bool) return value is
    begin
        return (0 => '1', 1 => data, others => '0');
    end;


  function magic_value(data : unit) return value is
    begin
        return (0 => '1', 1 => '1', others => '0');
    end;

  function magic_value(data : int) return value is
    begin
      return unsigned(data & "1");
    end;
  
  --function Bool_val(v : value) return bool;
  --function Int_val(v : value) return int;
  --function Val_int(n : int) return value;
  --function Val_bool(b : bool) return value;

  function ram_field(ram_start : value; addr : value; field:int) return value is
      begin
       return unsigned(signed(ram_start) +
                       signed("000" & addr(19 downto 0)) +
                       resize(signed(field(20 downto 0)) * 4,32));
       -- return (unsigned(ram_start) +
       --          unsigned(signed("000" & addr(19 downto 0)) +
       --                  signed(field(20 downto 0) & "00")));
      end;

  function size_hd(hd : header) return int is
      variable r : std_logic_vector(31 downto 0);
      begin
        r := std_logic_vector(hd);
        return signed("00000000000" & r(21 downto 2));
      end;

  function tag_hd(hd : header) return int is
    variable r : std_logic_vector(31 downto 0);
    begin
      r := std_logic_vector(hd);
      return signed("000" & "00000" & "00000" & "00000" & "00000" & r(31 downto 24));
    end;

  function as_immediate(v : value) return int is
    begin
      return signed(v(31 downto 1));
    end;

  function is_immediate(x : value) return bool is
  begin
    return x(0);
  end;

end;

