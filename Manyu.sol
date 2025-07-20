/*
 * SPDX-License-Identifier: MIT
 * https://manyushiba.com/
 * https://t.me/manyushiba
 * https://x.com/ManyuShiba
 */

pragma solidity 0.8.19;

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}

interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The default value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(
        address account
    ) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(
        address owner,
        address spender
    ) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(
        address spender,
        uint256 amount
    ) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the upd allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * Requirements:
     *
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);

        uint256 currentAllowance = _allowances[sender][_msgSender()];
        require(
            currentAllowance >= amount,
            "ERC20: transfer amount exceeds allowance"
        );
        unchecked {
            _approve(sender, _msgSender(), currentAllowance - amount);
        }

        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the upd allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(
        address spender,
        uint256 addedValue
    ) public virtual returns (bool) {
        _approve(
            _msgSender(),
            spender,
            _allowances[_msgSender()][spender] + addedValue
        );
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the upd allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(
        address spender,
        uint256 subtractedValue
    ) public virtual returns (bool) {
        uint256 currentAllowance = _allowances[_msgSender()][spender];
        require(
            currentAllowance >= subtractedValue,
            "ERC20: decreased allowance below zero"
        );
        unchecked {
            _approve(_msgSender(), spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `sender` to `recipient`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        uint256 senderBalance = _balances[sender];
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        unchecked {
            _balances[sender] = senderBalance - amount;
        }
        _balances[recipient] += amount;

        emit Transfer(sender, recipient, amount);

        _afterTokenTransfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
        }
        _totalSupply -= amount;

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}
}

abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

interface IDexFactory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    function feeTo() external view returns (address);

    function feeToSetter() external view returns (address);

    function getPair(
        address tokenA,
        address tokenB
    ) external view returns (address pair);

    function allPairs(uint256) external view returns (address pair);

    function allPairsLength() external view returns (uint256);

    function createPair(
        address tokenA,
        address tokenB
    ) external returns (address pair);

    function setFeeTo(address) external;

    function setFeeToSetter(address) external;
}

interface IDexRouter {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB, uint256 liquidity);

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (uint256 amountToken, uint256 amountETH, uint256 liquidity);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

contract Manyu is ERC20, Ownable {
    using SafeMath for uint256;

    IDexRouter private immutable uniRouter;
    address private immutable uniPair;

    // Swapback
    bool private onSwapback;

    bool private contractSBEnabled = false;
    uint256 private triggerSB;
    uint256 private limitSB;
    uint256 private lastSB;

    //Anti-whale
    bool private limitsEnabled = true;
    uint256 private maxWalletLimit;
    uint256 private maxTransactionLimit;

    bool private tradingOpen = false;

    // Fees
    address private projectWallet;

    uint256 private buyingFee;

    uint256 private sellingFee;

    uint256 private transferFee;
    /******************/

    // exclude from fees and max transaction amount
    mapping(address => bool) private exemptFromFees;
    mapping(address => bool) private exemptFromLimits;
    mapping(address => bool) private DEXPair;

    // store addresses that a automatic market maker pairs. Any transfer *to* these addresses
    // could be subject to a maximum transfer amount

    event ExemptFromFee(address indexed account, bool isExcluded);
    event ExemptFromLimit(address indexed account, bool isExcluded);
    event SetPairLPool(address indexed pair, bool indexed value);
    event TradingEnabled(uint256 indexed timestamp);
    event LimitsRemoved(uint256 indexed timestamp);

    event SwapbackSettingsUpdated(
        bool enabled,
        uint256 triggerSB,
        uint256 limitSB
    );
    event MaxTxUpdated(uint256 maxTransactionLimit);
    event MaxWalletUpdated(uint256 maxWalletLimit);

    event MarketingWalletUpdated(
        address indexed newWallet,
        address indexed oldWallet
    );

    event BuyFeeUpdated(
        uint256 buyingFee,
        uint256 buyMarketingTax,
        uint256 buyProjectTax
    );

    event SellFeeUpdated(
        uint256 sellingFee,
        uint256 sellMarketingTax,
        uint256 sellProjectTax
    );

    constructor() ERC20("Manyu", "MANYU") {
        IDexRouter _uniRouter = IDexRouter(
            0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D
        );

        changeLimitExemptAddress(address(_uniRouter), true);
        uniRouter = _uniRouter;

        uniPair = IDexFactory(_uniRouter.factory()).createPair(
            address(this),
            _uniRouter.WETH()
        );
        changeLimitExemptAddress(address(uniPair), true);
        _toggleDexPair(address(uniPair), true);

        uint256 _totalSupply = 1_000_000_000_000_000 * 10 ** decimals();

        lastSB = block.timestamp;

        maxTransactionLimit = (_totalSupply * 10) / 1000;
        maxWalletLimit = (_totalSupply * 10) / 1000;

        triggerSB = (_totalSupply * 1) / 1000;
        limitSB = (_totalSupply * 2) / 100;

        buyingFee = 30;

        sellingFee = 30;

        transferFee = 0;

        projectWallet = address(0x131Dbf30a9e3BAf253a2033Df26899e90E7F036F);

        // exclude from paying fees or having max transaction amount
        changeAddressFeeExempt(msg.sender, true);
        changeAddressFeeExempt(address(this), true);
        changeAddressFeeExempt(address(0xdead), true);
        changeAddressFeeExempt(projectWallet, true);

        changeLimitExemptAddress(msg.sender, true);
        changeLimitExemptAddress(address(this), true);
        changeLimitExemptAddress(address(0xdead), true);
        changeLimitExemptAddress(projectWallet, true);

        transferOwnership(msg.sender);

        /*
            _mint is an internal function in ERC20.sol that is only called here,
            and CANNOT be called ever again
        */
        _mint(msg.sender, _totalSupply);
    }

    receive() external payable {}

    function decimals() public view virtual override returns (uint8) {
        return 9;
    }

    /**
     * @notice  Opens public trading for the token
     * @dev     onlyOwner.
     */
    function openTrading() external onlyOwner {
        tradingOpen = true;
        contractSBEnabled = true;
        emit TradingEnabled(block.timestamp);
    }

    /**
     * @notice Removes the max wallet and max transaction limits
     * @dev onlyOwner.
     * Emits an {LimitsRemoved} event
     */
    function removeLimitsNow() external onlyOwner {
        limitsEnabled = false;
        transferFee = 0;
        emit LimitsRemoved(block.timestamp);
    }

    /**
     * @notice sets if swapback is enabled and sets the minimum and maximum amounts
     * @dev onlyOwner.
     * Emits an {SwapbackSettingsUpdated} event
     * @param _caSBcEnabled If swapback is enabled
     * @param _caSBcTrigger The minimum amount of tokens the contract must have before swapping tokens for ETH. Base 10000, so 1% = 100.
     * @param _caSBcLimit The maximum amount of tokens the contract can swap for ETH. Base 10000, so 1% = 100.
     */
    function changeValuesSwapback(
        bool _caSBcEnabled,
        uint256 _caSBcTrigger,
        uint256 _caSBcLimit
    ) external onlyOwner {
        require(
            _caSBcTrigger >= 1,
            "Swap amount cannot be lower than 0.01% total supply."
        );
        require(
            _caSBcLimit >= _caSBcTrigger,
            "maximum amount cant be higher than minimum"
        );

        contractSBEnabled = _caSBcEnabled;
        triggerSB = (totalSupply() * _caSBcTrigger) / 10000;
        limitSB = (totalSupply() * _caSBcLimit) / 10000;
        emit SwapbackSettingsUpdated(_caSBcEnabled, _caSBcTrigger, _caSBcLimit);
    }

    /**
     * @notice Changes the maximum amount of tokens that can be bought or sold in a single transaction
     * @dev onlyOwner.
     * Emits an {MaxTxUpdated} event
     * @param _maxTransactionLimit Base 1000, so 1% = 10
     */
    function maxLimitsChangeTxLimit(uint256 _maxTransactionLimit) external onlyOwner {
        require(_maxTransactionLimit >= 2, "Cannot set maxTransactionLimit lower than 0.2%");
        maxTransactionLimit = (_maxTransactionLimit * totalSupply()) / 1000;
        emit MaxTxUpdated(maxTransactionLimit);
    }

    /**
     * @notice Changes the maximum amount of tokens a wallet can hold
     * @dev onlyOwner.
     * Emits an {MaxWalletUpdated} event
     * @param _maxWalletLimit Base 1000, so 1% = 10
     */
    function maxLimitsChangeWalletLimit(
        uint256 _maxWalletLimit
    ) external onlyOwner {
        require(_maxWalletLimit >= 5, "Cannot set maxWalletLimit lower than 0.5%");
        maxWalletLimit = (_maxWalletLimit * totalSupply()) / 1000;
        emit MaxWalletUpdated(maxWalletLimit);
    }

    /**
     * @notice Sets if a wallet is excluded from the max wallet and tx limits
     * @dev onlyOwner.
     * Emits an {ExemptFromLimit} event
     * @param _add The wallet to update
     * @param _excluded If the wallet is excluded or not
     */
    function changeLimitExemptAddress(
        address _add,
        bool _excluded
    ) public onlyOwner {
        exemptFromLimits[_add] = _excluded;
        emit ExemptFromLimit(_add, _excluded);
    }

    /**
     * @notice Sets the fees for buys
     * @dev onlyOwner.
     * Emits a {BuyFeeUpdated} event
     * All fees added up must be less than 100
     * @param _value The fee for the marketing wallet
     */
    function changeFeeBuy(uint256 _value) external onlyOwner {
        buyingFee = _value;
        require(buyingFee <= 100, "Total buy fee cannot be higher than 100%");
        emit BuyFeeUpdated(buyingFee, buyingFee, buyingFee);
    }

    /**
     * @notice Sets the fees for sells
     * @dev onlyOwner.
     * Emits a {SellFeeUpdated} event
     * All fees added up must be less than 100
     * @param _value The fee for the marketing wallet
     */
    function changeFeeSell(uint256 _value) external onlyOwner {
        sellingFee = _value;
        require(
            sellingFee <= 100,
            "Total sell fee cannot be higher than 100%"
        );
        emit SellFeeUpdated(sellingFee, sellingFee, sellingFee);
    }

    function changeFeeTransfer(uint256 _value) external onlyOwner {
        transferFee = _value;
        require(
            transferFee <= 100,
            "Total transfer fee cannot be higher than 100%"
        );
    }

    /**
     * @notice Sets if an address is excluded from fees
     * @dev onlyOwner.
     * Emits an {ExemptFromFee} event
     * @param _add The wallet to update
     * @param _excluded If the wallet is excluded or not
     */
    function changeAddressFeeExempt(
        address _add,
        bool _excluded
    ) public onlyOwner {
        exemptFromFees[_add] = _excluded;
        emit ExemptFromFee(_add, _excluded);
    }

    function _toggleDexPair(address pair, bool value) private {
        DEXPair[pair] = value;

        emit SetPairLPool(pair, value);
    }

    /**
     * @notice Sets the marketing wallet
     * @dev onlyOwner.
     * Emits an {MarketingWalletUpdated} event
     * @param _marketing The new marketing wallet
     */
    function changeMarketingReceiver(address _marketing) external onlyOwner {
        emit MarketingWalletUpdated(_marketing, projectWallet);
        projectWallet = _marketing;
    }


    /**
     * @notice  Information about the swapback settings
     * @return  _contractSBEnabled  if swapback is enabled
     * @return  _caSBcackValueMin  the minimum amount of tokens in the contract balance to trigger swapback
     * @return  _caSBcackValueMax  the maximum amount of tokens in the contract balance to trigger swapback
     */
    function readSwapbackInfo()
        external
        view
        returns (
            bool _contractSBEnabled,
            uint256 _caSBcackValueMin,
            uint256 _caSBcackValueMax
        )
    {
        _contractSBEnabled = contractSBEnabled;
        _caSBcackValueMin = triggerSB;
        _caSBcackValueMax = limitSB;
    }

    /**
     * @notice  Information about the anti whale parameters
     * @return  _limitsEnabled  if the wallet limits are in effect
     * @return  _maxWalletLimit  The maximum amount of tokens that can be held by a wallet
     * @return  _maxTransactionLimit  The maximum amount of tokens that can be bought or sold in a single transaction
     */
    function readLimitInfo()
        external
        view
        returns (bool _limitsEnabled, uint256 _maxWalletLimit, uint256 _maxTransactionLimit)
    {
        _limitsEnabled = limitsEnabled;
        _maxWalletLimit = maxWalletLimit;
        _maxTransactionLimit = maxTransactionLimit;
    }

    /**
     * @notice The wallets that receive the collected fees
     * @return _projectWallet The wallet that receives the marketing fees
     */
    function readFeeReceiverAddress()
        external
        view
        returns (address _projectWallet)
    {
        return (projectWallet);
    }

    /**
     * @notice Fees for buys, sells, and transfers
     * @return _buyingFee The total fee for buys
     * @return _sellingFee The total fee for sells
     * @return _transferFee The total fee for transfers
     */
    function readFeesInfo()
        external
        view
        returns (
            uint256 _buyingFee,
            uint256 _sellingFee,
            uint256 _transferFee
        )
    {
        _buyingFee = buyingFee;
        _sellingFee = sellingFee;
        _transferFee = transferFee;
    }

    /**
     * @notice  If the wallet is excluded from fees and max transaction amount and if the wallet is a automated market maker pair
     * @param   _target  The wallet to check
     * @return  _exemptFromFees  If the wallet is excluded from fees
     * @return  _exemptFromLimits  If the wallet is excluded from max transaction amount
     * @return  _DEXPair If the wallet is a automated market maker pair
     */
    function readAddressInfo(
        address _target
    )
        external
        view
        returns (
            bool _exemptFromFees,
            bool _exemptFromLimits,
            bool _DEXPair
        )
    {
        _exemptFromFees = exemptFromFees[_target];
        _exemptFromLimits = exemptFromLimits[_target];
        _DEXPair = DEXPair[_target];
    }

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal override {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        if (amount == 0) {
            super._transfer(from, to, 0);
            return;
        }

        if (limitsEnabled) {
            if (
                from != owner() &&
                to != owner() &&
                to != address(0) &&
                to != address(0xdead) &&
                !onSwapback
            ) {
                if (!tradingOpen) {
                    require(
                        exemptFromFees[from] || exemptFromFees[to],
                        "_transfer:: Trading is not active."
                    );
                }

                //when buy
                if (
                    DEXPair[from] && !exemptFromLimits[to]
                ) {
                    require(
                        amount <= maxTransactionLimit,
                        "Buy transfer amount exceeds the maxTransactionLimit."
                    );
                    require(
                        amount + balanceOf(to) <= maxWalletLimit,
                        "Max wallet exceeded"
                    );
                }
                //when sell
                else if (
                    DEXPair[to] && !exemptFromLimits[from]
                ) {
                    require(
                        amount <= maxTransactionLimit,
                        "Sell transfer amount exceeds the maxTransactionLimit."
                    );
                } else if (!exemptFromLimits[to]) {
                    require(
                        amount + balanceOf(to) <= maxWalletLimit,
                        "Max wallet exceeded"
                    );
                }
            }
        }

        uint256 contractTokenBalance = balanceOf(address(this));

        bool canSwap = contractTokenBalance >= triggerSB;

        if (
            canSwap &&
            contractSBEnabled &&
            !onSwapback &&
            !DEXPair[from] &&
            !exemptFromFees[from] &&
            !exemptFromFees[to] &&
            lastSB != block.timestamp
        ) {
            onSwapback = true;

            swapBack(amount);

            lastSB = block.timestamp;

            onSwapback = false;
        }

        bool takeFee = !onSwapback;

        // if any account belongs to _isExcludedFromFee account then remove the fee
        if (exemptFromFees[from] || exemptFromFees[to]) {
            takeFee = false;
        }

        uint256 fees = 0;
        // only take fees on buys/sells, do not take on wallet transfers
        if (takeFee) {
            // on sell
            if (DEXPair[to] && sellingFee > 0) {
                fees = amount.mul(sellingFee).div(100);
            }
            // on buy
            else if (DEXPair[from] && buyingFee > 0) {
                fees = amount.mul(buyingFee).div(100);
            }
            // on transfers
            else if (
                transferFee > 0 &&
                !DEXPair[from] &&
                !DEXPair[to]
            ) {
                fees = amount.mul(transferFee).div(100);
            }

            if (fees > 0) {
                super._transfer(from, address(this), fees);
            }

            amount -= fees;
        }

        super._transfer(from, to, amount);
    }

    function swapTokensForEth(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = uniRouter.WETH();

        _approve(address(this), address(uniRouter), tokenAmount);

        // make the swap
        uniRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );
    }

    function swapBack(uint256 amount) private {
        uint256 contractBalance = balanceOf(address(this));
        bool success;

        if (contractBalance == 0) {
            return;
        }

        if (contractBalance > limitSB) {
            contractBalance = limitSB;
        }

        if (contractBalance > amount * 15) {
            contractBalance = amount * 15;
        }

        uint256 amountToSwapForETH = contractBalance;

        swapTokensForEth(amountToSwapForETH);

        (success, ) = address(projectWallet).call{
            value: address(this).balance
        }("");
    }
}